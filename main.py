#!/usr/bin/env python3
"""github-core-clone-01 entry: a standalone git forge (Python 3.13, stdlib only).

Serves, from ONE process with an in-memory store (no UI, no outside service):
  - git smart HTTP: clone / fetch / push (protocol v2 + v0 fallback), real git
    objects (commits round-trip byte-identical), packs (plain objects, no deltas
    needed on the wire out; deltas understood on the wire in), shallow deepen.
  - REST v3: repositories, branches, commits, contents, issues, comments,
    labels, pull requests, files, merges.
  - GraphQL v4: the documents gh and github-mcp-server send (viewer, repository,
    issues, pull requests, mutations, node(id:), __type introspection, batching).
  - MCP (streamable HTTP, 2026-07-28 server/discover + legacy initialize):
    create_repo, get_repo, create_issue, list_issues, create_pull_request,
    merge_pull_request.

Lifecycle (same as the starter main.ts): bind an ephemeral port, POST
$MAKEFUN_ENV_URL/register {"port": N}, poll GET $MAKEFUN_ENV_URL/done until
{"done": true}, then exit 0. Without MAKEFUN_ENV_URL it serves standalone on
FORGE_PORT (default 8123) for local testing.

Auth: every API call presents Authorization: Bearer $MAKEFUN_SHOP_TOKEN; the
token's owner is the viewer "adaiversen" (id 1000). A missing or wrong token
is a 401. /healthz needs no token.

SPDX-License-Identifier: MIT
"""

import base64
import difflib
import hashlib
import json
import os
import re
import secrets
import socket
import sys
import threading
import time
import urllib.request
import urllib.error
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import unquote, urlsplit, parse_qs
import zlib

VERSION = "1.0.0"
SERVER_NAME = "github-core-clone-forge"
VIEWER_LOGIN = "adaiversen"
VIEWER_ID = 1000
VIEWER_NAME = "ada iversen"
VIEWER_EMAIL = "adaiversen@example.invalid"
ZERO_OID = "0" * 40
DEFAULT_BRANCH = "main"
SHOP_TOKEN = os.environ.get("MAKEFUN_SHOP_TOKEN", "")

# ---------------------------------------------------------------------------
# small helpers
# ---------------------------------------------------------------------------

def now_iso():
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

def sha1_hex(data):
    return hashlib.sha1(data).hexdigest()

def is_oid(s):
    return isinstance(s, str) and len(s) == 40 and all(c in "0123456789abcdef" for c in s.lower())

def b64e(raw):
    return base64.b64encode(raw).decode("ascii")

def b64d(text):
    return base64.b64decode(text.encode("ascii"))

def gid(kind, *parts):
    """Opaque Relay global id: base64 of 'kind:part:part'."""
    return b64e(":".join([kind] + [str(p) for p in parts]).encode("utf-8"))

def ungid(text):
    try:
        raw = b64d(text).decode("utf-8")
    except Exception:
        return None
    parts = raw.split(":")
    if len(parts) < 2:
        return None
    return parts

# ---------------------------------------------------------------------------
# git objects: hashing, trees, commits, packs, pkt-lines
# ---------------------------------------------------------------------------

def hash_object(otype, data):
    header = ("%s %d\0" % (otype, len(data))).encode("ascii")
    return sha1_hex(header + data)

def build_tree(entries):
    """entries: list of (mode_str, name, oid_hex). Returns (tree_oid, tree_bytes).
    Sorts git-style: names compared with dirs treated as if ending in '/'."""
    def sort_key(entry):
        mode, name, _oid = entry
        return name + ("/" if mode == "40000" else "")
    out = bytearray()
    for mode, name, oid in sorted(entries, key=sort_key):
        out += ("%s %s\0" % (mode, name)).encode("utf-8")
        out += bytes.fromhex(oid)
    data = bytes(out)
    return hash_object("tree", data), data

def parse_tree(data):
    """Returns list of (mode_str, name, oid_hex)."""
    entries = []
    i = 0
    n = len(data)
    while i < n:
        sp = data.index(b" ", i)
        mode = data[i:sp].decode("ascii")
        nul = data.index(b"\0", sp)
        name = data[sp + 1:nul].decode("utf-8", "surrogateescape")
        oid = data[nul + 1:nul + 21].hex()
        entries.append((mode, name, oid))
        i = nul + 21
    return entries

IDENTITY = "forge <forge@localhost>"

def build_commit(tree_oid, parents, message, timestamp=None):
    ts = int(timestamp if timestamp is not None else time.time())
    lines = ["tree %s" % tree_oid]
    for p in parents:
        lines.append("parent %s" % p)
    lines.append("author %s %d +0000" % (IDENTITY, ts))
    lines.append("committer %s %d +0000" % (IDENTITY, ts))
    lines.append("")
    lines.append(message if message.endswith("\n") else message + "\n")
    return "".join(l + "\n" for l in lines).encode("utf-8")

def parse_commit(data):
    """Returns dict: tree, parents(list), message, author, committer."""
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    message = message.rstrip("\n")
    out = {"tree": None, "parents": [], "message": message, "author": "", "committer": ""}
    for line in head.split("\n"):
        if line.startswith("tree "):
            out["tree"] = line[5:].strip()
        elif line.startswith("parent "):
            out["parents"].append(line[7:].strip())
        elif line.startswith("author "):
            out["author"] = line[7:]
        elif line.startswith("committer "):
            out["committer"] = line[10:]
    return out

def parse_tag(data):
    """Returns dict: object, type, tag, tagger, message."""
    text = data.decode("utf-8", "surrogateescape")
    head, _, message = text.partition("\n\n")
    out = {"object": None, "type": None, "tag": None, "tagger": "", "message": message}
    for line in head.split("\n"):
        if line.startswith("object "):
            out["object"] = line[7:].strip()
        elif line.startswith("type "):
            out["type"] = line[5:].strip()
        elif line.startswith("tag "):
            out["tag"] = line[4:].strip()
        elif line.startswith("tagger "):
            out["tagger"] = line[7:]
    return out

# --- pack writing (plain objects, no deltas) --------------------------------

_TYPE_NUM = {"commit": 1, "tree": 2, "blob": 3, "tag": 4}
_NUM_TYPE = {1: "commit", 2: "tree", 3: "blob", 4: "tag", 6: "ofs-delta", 7: "ref-delta"}

def _pack_object_header(otype_num, size):
    out = bytearray()
    first = (otype_num << 4) | (size & 0x0F)
    size >>= 4
    if size:
        first |= 0x80
    out.append(first)
    while size:
        b = size & 0x7F
        size >>= 7
        if size:
            b |= 0x80
        out.append(b)
    return bytes(out)

def write_pack(objects):
    """objects: list of (otype, data_bytes). Returns pack bytes with trailer."""
    out = bytearray()
    out += b"PACK"
    out += (2).to_bytes(4, "big")
    out += len(objects).to_bytes(4, "big")
    for otype, data in objects:
        out += _pack_object_header(_TYPE_NUM[otype], len(data))
        out += zlib.compress(data)
    trailer = hashlib.sha1(bytes(out)).digest()
    out += trailer
    return bytes(out)

def verify_pack_checksum(pack):
    if len(pack) < 32:
        return False
    return hashlib.sha1(pack[:-20]).digest() == pack[-20:]

# --- pack reading (plain objects + ofs/ref deltas) ---------------------------

def _read_varint(data, pos):
    result = data[pos] & 0x7F
    pos += 1
    shift = 7
    while data[pos - 1] & 0x80:
        result |= (data[pos] & 0x7F) << shift
        pos += 1
        shift += 7
    return result, pos

def _read_ofs_offset(data, pos):
    b = data[pos]
    pos += 1
    result = b & 0x7F
    while b & 0x80:
        b = data[pos]
        pos += 1
        result = ((result + 1) << 7) | (b & 0x7F)
    return result, pos

def apply_delta(base, delta):
    """Apply a git binary delta to base bytes; returns the result bytes."""
    pos = 0
    src_size, pos = _read_varint(delta, pos)
    tgt_size, pos = _read_varint(delta, pos)
    if src_size != len(base):
        raise ValueError("delta base size mismatch")
    out = bytearray()
    while pos < len(delta):
        op = delta[pos]
        pos += 1
        if op & 0x80:
            offset = 0
            size = 0
            for i in range(4):
                if op & (1 << i):
                    offset |= delta[pos] << (8 * i)
                    pos += 1
            for i in range(3):
                if op & (0x10 << i):
                    size |= delta[pos] << (8 * i)
                    pos += 1
            if size == 0:
                size = 0x10000
            out += base[offset:offset + size]
        elif op:
            out += delta[pos:pos + op]
            pos += op
        else:
            raise ValueError("delta opcode 0")
    if len(out) != tgt_size:
        raise ValueError("delta target size mismatch")
    return bytes(out)

def read_pack(pack):
    """Parse a pack. Returns (objects, delta_count) where objects is a dict
    oid -> (otype, data). Raises ValueError on malformed input."""
    if len(pack) < 32 or pack[:4] != b"PACK":
        raise ValueError("not a pack")
    version = int.from_bytes(pack[4:8], "big")
    if version != 2:
        raise ValueError("unsupported pack version %d" % version)
    count = int.from_bytes(pack[8:12], "big")
    if not verify_pack_checksum(pack):
        raise ValueError("pack checksum mismatch")
    objects = {}
    order = []  # (offset, oid) in pack order, for ofs-delta resolution
    delta_count = 0
    pos = 12
    end = len(pack) - 20
    for _ in range(count):
        start = pos
        first = pack[pos]
        pos += 1
        otype_num = (first >> 4) & 0x07
        size = first & 0x0F
        shift = 4
        while first & 0x80:
            first = pack[pos]
            pos += 1
            size |= (first & 0x7F) << shift
            shift += 7
        if otype_num == 6:  # ofs-delta
            off, pos = _read_ofs_offset(pack, pos)
            base_off = start - off
            base_oid = None
            for (o_off, o_oid) in order:
                if o_off == base_off:
                    base_oid = o_oid
                    break
            if base_oid is None:
                raise ValueError("ofs-delta base not found")
            d = zlib.decompressobj()
            data = d.decompress(pack[pos:end])
            consumed = len(pack[pos:end]) - len(d.unused_data)
            pos += consumed
            base_type, base_data = objects[base_oid]
            result = apply_delta(base_data, data)
            oid = hash_object(base_type, result)
            objects[oid] = (base_type, result)
            order.append((start, oid))
            delta_count += 1
        elif otype_num == 7:  # ref-delta
            base_oid = pack[pos:pos + 20].hex()
            pos += 20
            if base_oid not in objects:
                raise ValueError("ref-delta base not in pack")
            d = zlib.decompressobj()
            data = d.decompress(pack[pos:end])
            consumed = len(pack[pos:end]) - len(d.unused_data)
            pos += consumed
            base_type, base_data = objects[base_oid]
            result = apply_delta(base_data, data)
            oid = hash_object(base_type, result)
            objects[oid] = (base_type, result)
            order.append((start, oid))
            delta_count += 1
        else:
            otype = _NUM_TYPE.get(otype_num)
            if otype is None:
                raise ValueError("unknown pack object type %d" % otype_num)
            d = zlib.decompressobj()
            data = d.decompress(pack[pos:end])
            consumed = len(pack[pos:end]) - len(d.unused_data)
            pos += consumed
            if len(data) != size:
                raise ValueError("pack object size mismatch")
            oid = hash_object(otype, data)
            objects[oid] = (otype, data)
            order.append((start, oid))
    return objects, delta_count

# --- pkt-lines ----------------------------------------------------------------

def pkt(data):
    if isinstance(data, str):
        data = data.encode("utf-8")
    return ("%04x" % (len(data) + 4)).encode("ascii") + data

FLUSH = b"0000"
DELIM = b"0001"

def encode_pkt_lines(lines):
    """lines: list of str | 'flush' | 'delim'."""
    out = bytearray()
    for line in lines:
        if line == "flush":
            out += FLUSH
        elif line == "delim":
            out += DELIM
        else:
            out += pkt(line)
    return bytes(out)

def decode_pkt_lines(data):
    """Returns list of ('data', bytes) | ('flush', None) | ('delim', None).
    Raises ValueError on a malformed pkt-line."""
    out = []
    pos = 0
    n = len(data)
    while pos < n:
        if pos + 4 > n:
            raise ValueError("truncated pkt-line length")
        try:
            length = int(data[pos:pos + 4].decode("ascii"), 16)
        except ValueError:
            raise ValueError("bad pkt-line length %r" % data[pos:pos + 4])
        if length == 0:
            out.append(("flush", None))
            pos += 4
        elif length == 1:
            out.append(("delim", None))
            pos += 4
        elif length < 4:
            raise ValueError("pkt-line length %d < 4" % length)
        elif pos + length > n:
            raise ValueError("truncated pkt-line payload")
        else:
            out.append(("data", data[pos + 4:pos + length]))
            pos += length
    return out

def sideband_pack(pack, chunk=32768):
    """Frame pack bytes as sideband band-1 pkt-lines."""
    out = bytearray()
    for i in range(0, len(pack), chunk):
        out += pkt(b"\x01" + pack[i:i + chunk])
    return bytes(out)

# ---------------------------------------------------------------------------
# store: repositories, issues, pull requests (all in memory)
# ---------------------------------------------------------------------------

class Issue:
    __slots__ = ("number", "id", "title", "body", "state", "labels", "comments",
                 "created_at", "updated_at")

    def __init__(self, number, gid_num, title, body):
        self.number = number
        self.id = gid_num
        self.title = title
        self.body = body
        self.state = "open"
        self.labels = []  # list of label names
        self.comments = []  # list of Comment
        self.created_at = now_iso()
        self.updated_at = self.created_at

class Comment:
    __slots__ = ("id", "body", "created_at")

    def __init__(self, cid, body):
        self.id = cid
        self.body = body
        self.created_at = now_iso()

class PullRequest:
    __slots__ = ("number", "id", "title", "body", "head", "base", "base_sha",
                 "state", "merged", "merged_at", "merge_commit_sha",
                 "created_at", "updated_at")

    def __init__(self, number, gid_num, title, body, head, base, base_sha):
        self.number = number
        self.id = gid_num
        self.title = title
        self.body = body
        self.head = head
        self.base = base
        self.base_sha = base_sha
        self.state = "open"
        self.merged = False
        self.merged_at = None
        self.merge_commit_sha = None
        self.created_at = now_iso()
        self.updated_at = self.created_at

class Repo:
    def __init__(self, owner, name, private, description, database_id):
        self.owner = owner
        self.name = name
        self.private = bool(private)
        self.description = description or ""
        self.database_id = database_id
        self.default_branch = DEFAULT_BRANCH
        self.created_at = now_iso()
        self.updated_at = self.created_at
        self.refs = {}          # refname -> oid hex
        self.objects = {}       # oid -> (otype, data)
        self._filemaps = {}     # commit oid -> {path: (mode, blob_oid)}
        self.issues = []        # Issue, creation order
        self.next_issue_number = 1
        self.next_comment_id = 1
        self.labels = {}        # name -> color
        self.pulls = []         # PullRequest, creation order
        self.next_pr_number = 1
        self._pack_cache = {}   # (wants, depth, haves, shallow) -> pack bytes

    # -- git objects ---------------------------------------------------------
    def put_object(self, otype, data):
        oid = hash_object(otype, data)
        if oid not in self.objects:
            self.objects[oid] = (otype, data)
        return oid

    def get_object(self, oid):
        return self.objects.get(oid)

    def head_oid(self):
        return self.refs.get("refs/heads/" + self.default_branch)

    def ref_tip(self, refname):
        return self.refs.get(refname)

    # -- file maps -----------------------------------------------------------
    def filemap_of(self, commit_oid):
        """{path: (mode, blob_oid)} for a commit; computed lazily from trees."""
        cached = self._filemaps.get(commit_oid)
        if cached is not None:
            return cached
        obj = self.objects.get(commit_oid)
        if obj is None or obj[0] != "commit":
            return {}
        commit = parse_commit(obj[1])
        tree_oid = commit["tree"]
        result = {}
        self._walk_tree(tree_oid, "", result)
        self._filemaps[commit_oid] = result
        return result

    def _walk_tree(self, tree_oid, prefix, result):
        obj = self.objects.get(tree_oid)
        if obj is None or obj[0] != "tree":
            return
        for mode, name, oid in parse_tree(obj[1]):
            path = prefix + name
            if mode == "40000":
                self._walk_tree(oid, path + "/", result)
            else:
                result[path] = (mode, oid)

    def build_tree(self, filemap):
        """Build nested tree objects for a flat {path: (mode, blob_oid)} map.
        Returns the root tree oid; stores every tree object."""
        # group by directory
        def build(paths):
            entries = []
            dirs = {}
            for path in sorted(paths):
                first, _, rest = path.partition("/")
                if rest:
                    dirs.setdefault(first, []).append(rest)
                else:
                    mode, oid = paths[path]
                    entries.append((mode, first, oid))
            for dname, sub in sorted(dirs.items()):
                submap = {subpath: paths[dname + "/" + subpath] for subpath in sub}
                sub_oid = build(submap)
                entries.append(("40000", dname, sub_oid))
            oid, data = build_tree(entries)
            self.put_object("tree", data)
            return oid
        return build(filemap)

    def commit_files(self, tree_oid, parents, message, timestamp=None):
        data = build_commit(tree_oid, parents, message, timestamp)
        oid = self.put_object("commit", data)
        return oid

    def resolve_ref(self, ref):
        """Resolve a branch name, full ref, or commit oid to a commit oid."""
        if ref is None:
            return self.head_oid()
        if is_oid(ref):
            obj = self.objects.get(ref)
            if obj is not None and obj[0] == "commit":
                return ref
            return None
        if ref.startswith("refs/"):
            oid = self.refs.get(ref)
            return self._peel_to_commit(oid) if oid else None
        oid = self.refs.get("refs/heads/" + ref)
        if oid:
            return self._peel_to_commit(oid)
        return None

    def _peel_to_commit(self, oid):
        seen = 0
        while oid and seen < 10:
            obj = self.objects.get(oid)
            if obj is None:
                return None
            if obj[0] == "commit":
                return oid
            if obj[0] == "tag":
                oid = parse_tag(obj[1])["object"]
                seen += 1
                continue
            return None
        return None

    def peel_tag(self, oid):
        """If oid is an annotated tag object, return its target commit oid."""
        obj = self.objects.get(oid)
        if obj is None or obj[0] != "tag":
            return None
        return self._peel_to_commit(parse_tag(obj[1])["object"])

    def ancestors(self, commit_oid, limit=None):
        """All ancestors of commit_oid (including itself), BFS by parent links."""
        seen = set()
        stack = [commit_oid]
        while stack:
            cur = stack.pop()
            if cur in seen or cur is None:
                continue
            seen.add(cur)
            if limit is not None and len(seen) >= limit:
                break
            obj = self.objects.get(cur)
            if obj is None or obj[0] != "commit":
                continue
            stack.extend(parse_commit(obj[1])["parents"])
        return seen

    def is_ancestor(self, anc, desc):
        if anc == desc:
            return True
        if anc is None or desc is None:
            return False
        return anc in self.ancestors(desc)

    def commit_list(self, tip):
        """Commits reachable from tip, newest-first by timestamp then discovery."""
        if tip is None:
            return []
        seen = []
        seen_set = set()
        stack = [tip]
        commits = []
        while stack:
            cur = stack.pop()
            if cur in seen_set or cur is None:
                continue
            seen_set.add(cur)
            obj = self.objects.get(cur)
            if obj is None or obj[0] != "commit":
                continue
            parsed = parse_commit(obj[1])
            commits.append((cur, parsed))
            stack.extend(parsed["parents"])
        # order: by author timestamp desc, then discovery order is fine
        def ts(item):
            m = re.search(r" (\d+) \+0000$", item[1].get("author", ""))
            return int(m.group(1)) if m else 0
        commits.sort(key=ts, reverse=True)
        return [oid for oid, _ in commits]

class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.repos = {}  # (owner, name) -> Repo
        self._repo_counter = 0
        self._issue_counter = 0
        self._pr_counter = 0
        self._comment_counter = 0

    def next_repo_id(self):
        self._repo_counter += 1
        return self._repo_counter

    def next_issue_id(self):
        self._issue_counter += 1
        return self._issue_counter

    def next_pr_id(self):
        self._pr_counter += 1
        return self._pr_counter

    def next_comment_id(self):
        self._comment_counter += 1
        return self._comment_counter

    def create_repo(self, owner, name, private, description):
        repo = Repo(owner, name, private, description, self.next_repo_id())
        self.repos[(owner, name)] = repo
        return repo

    def get_repo(self, owner, name):
        return self.repos.get((owner, name))

    def delete_repo(self, owner, name):
        self.repos.pop((owner, name), None)

    def viewer_repos(self):
        return [r for (o, _n), r in sorted(self.repos.items()) if o == VIEWER_LOGIN]

STORE = Store()

# ---------------------------------------------------------------------------
# diff helpers (for pull-request files)
# ---------------------------------------------------------------------------

def _text_lines(data):
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        text = data.decode("utf-8", "replace")
    return text.splitlines()

def diff_file_counts(old_data, new_data):
    """(additions, deletions) between two blobs, by line diff."""
    old = _text_lines(old_data or b"")
    new = _text_lines(new_data or b"")
    sm = difflib.SequenceMatcher(a=old, b=new, autojunk=False)
    additions = 0
    deletions = 0
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == "insert":
            additions += j2 - j1
        elif tag == "delete":
            deletions += i2 - i1
        elif tag == "replace":
            additions += j2 - j1
            deletions += i2 - i1
    return additions, deletions

def pr_changed_files(repo, base_commit, head_commit):
    """List of {filename, status, additions, deletions, changes} for the diff
    base_commit -> head_commit. status: added | removed | modified."""
    base_map = repo.filemap_of(base_commit) if base_commit else {}
    head_map = repo.filemap_of(head_commit) if head_commit else {}
    out = []
    for path in sorted(set(base_map) | set(head_map)):
        in_base = path in base_map
        in_head = path in head_map
        if in_base and not in_head:
            old_data = repo.objects[base_map[path][1]][1]
            additions, deletions = diff_file_counts(old_data, b"")
            out.append({"filename": path, "status": "removed",
                        "additions": additions, "deletions": deletions,
                        "changes": additions + deletions})
        elif in_head and not in_base:
            new_data = repo.objects[head_map[path][1]][1]
            additions, deletions = diff_file_counts(b"", new_data)
            out.append({"filename": path, "status": "added",
                        "additions": additions, "deletions": deletions,
                        "changes": additions + deletions})
        else:
            if base_map[path][1] == head_map[path][1]:
                continue
            old_data = repo.objects[base_map[path][1]][1]
            new_data = repo.objects[head_map[path][1]][1]
            additions, deletions = diff_file_counts(old_data, new_data)
            out.append({"filename": path, "status": "modified",
                        "additions": additions, "deletions": deletions,
                        "changes": additions + deletions})
    return out

def pr_merge_conflict(repo, pr):
    """True when the base branch moved under the PR's changed files."""
    if pr.base_sha is None:
        return False
    base_tip = repo.ref_tip("refs/heads/" + pr.base)
    if base_tip is None:
        return False
    head_tip = repo.ref_tip("refs/heads/" + pr.head)
    if head_tip is None:
        return False
    changed = pr_changed_files(repo, pr.base_sha, head_tip)
    base_map = repo.filemap_of(pr.base_sha)
    current_map = repo.filemap_of(base_tip)
    for entry in changed:
        path = entry["filename"]
        if base_map.get(path, (None, None))[1] != current_map.get(path, (None, None))[1]:
            return True
    return False

# ---------------------------------------------------------------------------
# git smart HTTP protocol
# ---------------------------------------------------------------------------

AGENT = "forge/1.0"
UPLOAD_CAPS_V0 = ("side-band-64k thin-pack ofs-delta agent=%s "
                  "symref=HEAD:refs/heads/main shallow multi_ack multi_ack_detailed" % AGENT)
RECEIVE_CAPS_V0 = "report-status side-band-64k delete-refs ofs-delta agent=%s" % AGENT

def sorted_refs(repo):
    """[(refname, oid)] — HEAD first conceptually, then refs sorted."""
    return sorted(repo.refs.items())

def advertisement_v0(repo, service):
    """v0 info/refs body."""
    caps = UPLOAD_CAPS_V0 if service == "git-upload-pack" else RECEIVE_CAPS_V0
    out = bytearray()
    out += pkt("# service=%s\n" % service)
    out += FLUSH
    refs = sorted_refs(repo)
    head_oid = repo.refs.get("refs/heads/" + repo.default_branch, ZERO_OID)
    if not refs:
        out += pkt("%s capabilities^{}\0%s\n" % (ZERO_OID, caps))
    else:
        first = True
        out += pkt("%s HEAD\0%s\n" % (head_oid, caps))
        for name, oid in refs:
            out += pkt("%s %s\n" % (oid, name))
    out += FLUSH
    return bytes(out)

def advertisement_v2(repo):
    out = bytearray()
    out += pkt("version 2\n")
    out += pkt("agent=%s\n" % AGENT)
    out += pkt("ls-refs=unborn\n")
    out += pkt("fetch=shallow filter\n")
    out += pkt("object-format=sha1\n")
    out += FLUSH
    return bytes(out)

def ls_refs_response(repo, args):
    """args: dict with peel(bool), unborn(bool), symrefs(bool), prefixes(list)."""
    prefixes = args.get("prefixes", [])
    peel = args.get("peel", False)
    include_head = True
    if prefixes:
        include_head = any("HEAD".startswith(p) or p.startswith("HEAD") for p in prefixes)
    out = bytearray()
    head_oid = repo.refs.get("refs/heads/" + repo.default_branch)
    if include_head:
        if head_oid is None:
            out += pkt("unborn HEAD symref-target:refs/heads/%s\n" % repo.default_branch)
        else:
            out += pkt("%s HEAD symref-target:refs/heads/%s\n" % (head_oid, repo.default_branch))
    for name, oid in sorted_refs(repo):
        if prefixes and not any(name.startswith(p) for p in prefixes):
            continue
        line = "%s %s" % (oid, name)
        if peel:
            peeled = repo.peel_tag(oid)
            if peeled:
                line += " peeled:%s" % peeled
        out += pkt(line + "\n")
    out += FLUSH
    return bytes(out)

def fetch_closure(repo, wants, haves, client_shallow, depth):
    """Compute the objects a fetch must send.

    Returns (send_commits, send_objects, shallow_list, unshallow_list) where
    send_objects is a dict oid -> (otype, data) and shallow_list names the new
    shallow boundaries. haves are excluded with their full ancestry, except
    traversal stops at the client's shallow boundaries (the client holds the
    boundary commit but not its parents)."""
    # excluded: ancestors of haves, not passing through shallow boundaries
    excluded = set()
    stack = list(haves)
    while stack:
        cur = stack.pop()
        if cur in excluded or cur is None:
            continue
        obj = repo.objects.get(cur)
        if obj is None or obj[0] != "commit":
            continue
        excluded.add(cur)
        if cur in client_shallow:
            continue
        stack.extend(parse_commit(obj[1])["parents"])
    # Expand tag wants: a want naming an annotated tag sends the tag
    # object itself (and any tag chain) plus a walk of its target commit.
    tag_oids = set()
    commit_wants = []
    for w in wants:
        obj = repo.objects.get(w)
        chain = []
        cur = w
        while obj is not None and obj[0] == "tag":
            chain.append(cur)
            cur = parse_tag(obj[1])["object"]
            obj = repo.objects.get(cur)
        tag_oids.update(chain)
        if obj is not None and obj[0] == "commit":
            commit_wants.append(cur)
    wants = commit_wants
    # wanted commits within the depth limit, minus excluded
    send_commits = set()
    boundary = set()
    if depth is None:
        stack = [(w, 0) for w in wants]
        seen = set()
        while stack:
            cur, _d = stack.pop()
            if cur in seen or cur is None:
                continue
            seen.add(cur)
            obj = repo.objects.get(cur)
            if obj is None or obj[0] != "commit":
                continue
            if cur not in excluded:
                send_commits.add(cur)
            stack.extend((p, 0) for p in parse_commit(obj[1])["parents"])
    else:
        # BFS by distance from any want
        dist = {}
        queue = [(w, 0) for w in wants if repo.objects.get(w, (None,))[0] == "commit"]
        head = 0
        while head < len(queue):
            cur, d = queue[head]
            head += 1
            if cur in dist:
                continue
            dist[cur] = d
            if d >= depth:
                continue
            obj = repo.objects.get(cur)
            if obj is None or obj[0] != "commit":
                continue
            for p in parse_commit(obj[1])["parents"]:
                if p not in dist:
                    queue.append((p, d + 1))
        for oid, d in dist.items():
            if d < depth and oid not in excluded:
                send_commits.add(oid)
            if d == depth - 1 and oid not in excluded:
                obj = repo.objects.get(oid)
                if obj is not None and obj[0] == "commit":
                    parents = parse_commit(obj[1])["parents"]
                    if parents and not all(p in excluded or p in send_commits for p in parents):
                        boundary.add(oid)
    # unshallow: client shallow boundaries whose parents are now all
    # sent-or-excluded (their history is complete).
    unshallow = set()
    for oid in client_shallow:
        obj = repo.objects.get(oid)
        if obj is None or obj[0] != "commit":
            continue
        parents = parse_commit(obj[1])["parents"]
        if parents and all(p in excluded or p in send_commits for p in parents):
            unshallow.add(oid)
    # collect trees + blobs reachable from send_commits, minus anything
    # reachable from excluded commits
    excluded_objects = set()
    for commit_oid in excluded:
        obj = repo.objects.get(commit_oid)
        if obj is None or obj[0] != "commit":
            continue
        tree_oid = parse_commit(obj[1])["tree"]
        excluded_objects |= _tree_objects(repo, tree_oid)
        excluded_objects.add(commit_oid)
    send_objects = {}
    for commit_oid in send_commits:
        send_objects[commit_oid] = repo.objects[commit_oid]
        obj = repo.objects.get(commit_oid)
        tree_oid = parse_commit(obj[1])["tree"]
        for oid in _tree_objects(repo, tree_oid):
            if oid not in excluded_objects and oid not in send_objects:
                send_objects[oid] = repo.objects[oid]
    # tag objects named by a want are sent even when their target commit
    # is already held by the client.
    for oid in tag_oids:
        if oid in repo.objects and oid not in send_objects:
            send_objects[oid] = repo.objects[oid]
    return send_commits, send_objects, sorted(boundary), sorted(unshallow)

def _tree_objects(repo, tree_oid):
    """All object oids reachable from a tree (tree + subtrees + blobs)."""
    out = set()
    stack = [tree_oid]
    while stack:
        cur = stack.pop()
        if cur in out or cur is None:
            continue
        obj = repo.objects.get(cur)
        if obj is None:
            continue
        out.add(cur)
        if obj[0] == "tree":
            for mode, _name, oid in parse_tree(obj[1]):
                stack.append(oid)
    return out

def fetch_pack(repo, wants, haves, client_shallow, depth):
    """Returns (pack_bytes_or_None, shallow, unshallow, acks, nak)."""
    cache_key = (tuple(sorted(wants)), depth, tuple(sorted(haves)),
                 tuple(sorted(client_shallow)))
    cached = repo._pack_cache.get(cache_key)
    _send, send_objects, shallow, unshallow = fetch_closure(
        repo, wants, haves, set(client_shallow), depth)
    acks = [h for h in haves if h in repo.objects]
    nak = not acks
    if not send_objects:
        # fetch-nothing-new: real git still sends an empty pack (0 objects)
        # inside the packfile section, never an absent section.
        return write_pack([]), shallow, unshallow, acks, nak
    if cached is not None:
        pack = cached
    else:
        ordered = []
        # commits first (discovery order), then trees, then blobs — any order
        # parses; keep it deterministic.
        for oid in sorted(send_objects):
            otype, data = send_objects[oid]
            if otype == "commit":
                ordered.append((otype, data))
        for oid in sorted(send_objects):
            otype, data = send_objects[oid]
            if otype == "tree":
                ordered.append((otype, data))
        for oid in sorted(send_objects):
            otype, data = send_objects[oid]
            if otype == "blob":
                ordered.append((otype, data))
        for oid in sorted(send_objects):
            otype, data = send_objects[oid]
            if otype == "tag":
                ordered.append((otype, data))
        pack = write_pack(ordered)
        if len(repo._pack_cache) < 64:
            repo._pack_cache[cache_key] = pack
    return pack, shallow, unshallow, acks, nak

def v2_fetch_response(repo, wants, haves, client_shallow, depth, done=True):
    """v2 fetch response, matching real git (verified against git 2.43.0
    upload-pack --stateless-rpc):
    - When the request carries `done`, negotiation is over: NO
      acknowledgments section is sent at all (real git sends none, even
      when haves were given); only shallow-info (if any) then packfile.
    - When `done` is absent, negotiation is still open: answer with the
      acknowledgments section only (NAK, or ACKs + ready) and no packfile.
    The packfile section is always present once done (an empty 0-object
    pack for fetch-nothing-new)."""
    pack, shallow, unshallow, acks, nak = fetch_pack(
        repo, wants, haves, client_shallow, depth)
    out = bytearray()
    if not done:
        out += pkt("acknowledgments\n")
        if nak:
            out += pkt("NAK\n")
        else:
            for ack in acks:
                out += pkt("ACK %s\n" % ack)
            out += pkt("ready\n")
        out += FLUSH
        return bytes(out)
    if shallow or unshallow:
        out += pkt("shallow-info\n")
        for oid in shallow:
            out += pkt("shallow %s\n" % oid)
        for oid in unshallow:
            out += pkt("unshallow %s\n" % oid)
        out += DELIM
    out += pkt("packfile\n")
    out += sideband_pack(pack)
    out += FLUSH
    return bytes(out)

def v0_fetch_response(repo, wants, haves, client_shallow, depth):
    pack, shallow, unshallow, acks, nak = fetch_pack(
        repo, wants, haves, client_shallow, depth)
    out = bytearray()
    if nak:
        out += pkt("NAK\n")
    else:
        for ack in acks:
            out += pkt("ACK %s\n" % ack)
    for oid in shallow:
        out += pkt("shallow %s\n" % oid)
    for oid in unshallow:
        out += pkt("unshallow %s\n" % oid)
    if pack is not None:
        out += sideband_pack(pack)
    out += FLUSH
    return bytes(out)

def parse_v2_request(data):
    """Parse a v2 upload-pack request body. Returns (command, args_dict)."""
    packets = decode_pkt_lines(data)
    lines = []
    for kind, payload in packets:
        if kind == "data":
            lines.append(payload.decode("utf-8", "surrogateescape"))
        elif kind == "delim":
            lines.append("\x01")
        elif kind == "flush":
            lines.append("\x00")
    command = None
    args = {"wants": [], "haves": [], "shallow": [], "depth": None,
            "peel": False, "unborn": False, "symrefs": False, "prefixes": [],
            "filter": None, "done": False}
    for line in lines:
        line = line.rstrip("\n")
        if line.startswith("command="):
            command = line[8:]
        elif line == "peel":
            args["peel"] = True
        elif line == "unborn":
            args["unborn"] = True
        elif line == "symrefs":
            args["symrefs"] = True
        elif line.startswith("ref-prefix "):
            args["prefixes"].append(line[11:])
        elif line.startswith("want "):
            args["wants"].append(line[5:].strip())
        elif line.startswith("have "):
            args["haves"].append(line[5:].strip())
        elif line.startswith("shallow "):
            args["shallow"].append(line[8:].strip())
        elif line.startswith("deepen "):
            try:
                args["depth"] = int(line[7:].strip())
            except ValueError:
                pass
        elif line.startswith("filter "):
            args["filter"] = line[7:].strip()
        elif line == "done":
            args["done"] = True
    return command, args

def parse_v0_fetch(data):
    """Parse a v0 upload-pack request. Returns (wants, haves, shallow, depth)."""
    packets = decode_pkt_lines(data)
    wants, haves, shallow, depth = [], [], [], None
    section = 0
    for kind, payload in packets:
        if kind == "flush":
            section += 1
            continue
        if kind != "data":
            continue
        line = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if line.startswith("want "):
            wants.append(line[5:].split()[0])
        elif line.startswith("shallow "):
            shallow.append(line[8:].strip())
        elif line.startswith("deepen "):
            try:
                depth = int(line[7:].strip())
            except ValueError:
                pass
        elif line.startswith("have "):
            haves.append(line[5:].strip())
    return wants, haves, shallow, depth

def handle_receive_pack(repo, body):
    """Process a git-receive-pack POST body. Returns the response bytes.
    Honors report-status + side-band-64k when the client asked for them.
    The body is a pkt-line command list, a flush, then raw pack bytes, so it
    is scanned by hand: a generic pkt-line decode would choke on the pack."""
    # command list: pkt-lines up to the first flush; the rest is the pack
    commands = []
    capabilities = set()
    pack = b""
    pos = 0
    n = len(body)
    while pos < n:
        if pos + 4 > n:
            return None
        try:
            length = int(body[pos:pos + 4].decode("ascii"), 16)
        except ValueError:
            return None
        if length == 0:
            pos += 4
            pack = body[pos:]
            break
        if length == 1:
            pos += 4
            continue
        if length < 4 or pos + length > n:
            return None
        payload = body[pos + 4:pos + length]
        pos += length
        text = payload.decode("utf-8", "surrogateescape").rstrip("\n")
        if "\x00" in text:
            cmd_part, _, caps_part = text.partition("\x00")
            for cap in caps_part.split(" "):
                if cap:
                    capabilities.add(cap.split("=")[0])
            text = cmd_part
        parts = text.split(" ")
        if len(parts) == 3 and is_oid(parts[0]) and is_oid(parts[1]):
            commands.append((parts[0], parts[1], parts[2]))
    if not commands:
        return None
    sideband = "side-band-64k" in capabilities
    report_status = "report-status" in capabilities or "report-status-v2" in capabilities
    # unpack: store every object the pack carries, even for refused refs
    unpack_ok = True
    unpack_detail = "ok"
    if pack:
        try:
            objects, _deltas = read_pack(pack)
            for oid, (otype, data) in objects.items():
                repo.put_object(otype, data)
        except ValueError as err:
            unpack_ok = False
            unpack_detail = str(err)[:120] or "unpack error"
    else:
        # a create/update command list with no pack is an unpack error;
        # a delete-only list needs no pack
        if any(new != ZERO_OID for _old, new, _ref in commands):
            unpack_ok = False
            unpack_detail = "unpacker error"
    report_lines = []
    if unpack_ok:
        report_lines.append("unpack ok")
    else:
        report_lines.append("unpack " + unpack_detail)
    for old_oid, new_oid, ref in commands:
        if not unpack_ok:
            report_lines.append("ng %s unpack failed" % ref)
            continue
        ok, reason = apply_push(repo, old_oid, new_oid, ref)
        if ok:
            report_lines.append("ok %s" % ref)
        else:
            report_lines.append("ng %s %s" % (ref, reason))
    if not report_status:
        # without report-status the client still reads a report; send it raw
        body_out = encode_pkt_lines([l + "\n" for l in report_lines] + ["flush"])
        return body_out
    inner = encode_pkt_lines([l + "\n" for l in report_lines] + ["flush"])
    if sideband:
        out = bytearray()
        # split the inner report into sideband packets (one per line is fine)
        for line in report_lines:
            out += pkt(b"\x01" + pkt(line + "\n"))
        out += pkt(b"\x01" + FLUSH)
        out += FLUSH
        return bytes(out)
    return inner

def apply_push(repo, old_oid, new_oid, ref):
    """Apply one push command. Returns (ok, reason)."""
    current = repo.refs.get(ref)
    if new_oid == ZERO_OID:
        # delete
        if current is None:
            return False, "remote ref does not exist"
        if old_oid != ZERO_OID and old_oid != current:
            return False, "non-fast-forward"
        del repo.refs[ref]
        repo._pack_cache.clear()
        return True, ""
    obj = repo.objects.get(new_oid)
    if obj is None:
        return False, "missing object"
    if current is None:
        if old_oid != ZERO_OID:
            return False, "non-fast-forward"
        repo.refs[ref] = new_oid
        repo._pack_cache.clear()
        return True, ""
    if old_oid != current:
        return False, "non-fast-forward"
    if not repo.is_ancestor(current, new_oid):
        return False, "non-fast-forward"
    repo.refs[ref] = new_oid
    repo._pack_cache.clear()
    return True, ""

# ---------------------------------------------------------------------------
# REST v3 serialization
# ---------------------------------------------------------------------------

def user_json():
    return {"login": VIEWER_LOGIN, "id": VIEWER_ID, "type": "User",
            "name": VIEWER_NAME, "email": VIEWER_EMAIL}

def repo_json(repo):
    return {
        "id": repo.database_id,
        "name": repo.name,
        "full_name": "%s/%s" % (repo.owner, repo.name),
        "owner": user_json(),
        "private": repo.private,
        "description": repo.description,
        "default_branch": repo.default_branch,
        "created_at": repo.created_at,
        "updated_at": repo.updated_at,
        "pushed_at": repo.updated_at,
        "html_url": "https://example.invalid/%s/%s" % (repo.owner, repo.name),
        "url": "/api/v3/repos/%s/%s" % (repo.owner, repo.name),
        "clone_url": "https://example.invalid/%s/%s.git" % (repo.owner, repo.name),
        "git_url": "git://example.invalid/%s/%s.git" % (repo.owner, repo.name),
        "has_issues": True,
        "has_projects": True,
        "has_wiki": True,
        "fork": False,
        "archived": False,
        "disabled": False,
    }

def issue_json(repo, issue):
    return {
        "id": issue.id,
        "number": issue.number,
        "title": issue.title,
        "body": issue.body,
        "state": issue.state,
        "labels": [{"name": name, "color": repo.labels.get(name, "ededed")}
                   for name in issue.labels],
        "user": user_json(),
        "created_at": issue.created_at,
        "updated_at": issue.updated_at,
        "url": "/api/v3/repos/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number),
        "html_url": "https://example.invalid/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number),
        "comments_url": "/api/v3/repos/%s/%s/issues/%d/comments" % (repo.owner, repo.name, issue.number),
    }

def comment_json(repo, issue, comment):
    return {
        "id": comment.id,
        "body": comment.body,
        "user": user_json(),
        "created_at": comment.created_at,
        "updated_at": comment.created_at,
        "issue_url": "/api/v3/repos/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number),
    }

def pull_json(repo, pr):
    head_sha = repo.ref_tip("refs/heads/" + pr.head) or ZERO_OID
    base_sha = repo.ref_tip("refs/heads/" + pr.base) or ZERO_OID
    return {
        "id": pr.id,
        "number": pr.number,
        "title": pr.title,
        "body": pr.body,
        "state": pr.state,
        "merged": pr.merged,
        "merged_at": pr.merged_at,
        "merge_commit_sha": pr.merge_commit_sha,
        "head": {"ref": pr.head, "sha": head_sha,
                 "label": "%s:%s" % (repo.owner, pr.head)},
        "base": {"ref": pr.base, "sha": base_sha,
                 "label": "%s:%s" % (repo.owner, pr.base)},
        "user": user_json(),
        "created_at": pr.created_at,
        "updated_at": pr.updated_at,
        "url": "/api/v3/repos/%s/%s/pulls/%d" % (repo.owner, repo.name, pr.number),
        "html_url": "https://example.invalid/%s/%s/pull/%d" % (repo.owner, repo.name, pr.number),
    }

def paginate(items, query):
    """(page_items, link_header_or_None, total). query: dict of str->str."""
    try:
        per_page = int(query.get("per_page", ["30"])[0])
    except (ValueError, IndexError):
        per_page = 30
    per_page = max(1, min(per_page, 100))
    try:
        page = int(query.get("page", ["1"])[0])
    except (ValueError, IndexError):
        page = 1
    page = max(1, page)
    total = len(items)
    start = (page - 1) * per_page
    end = start + per_page
    return items[start:end], per_page, page, total

def link_header(base_url, path, query, per_page, page, total):
    """Build a GitHub-style Link header with absolute same-origin URLs."""
    last_page = max(1, (total + per_page - 1) // per_page)
    def url(p):
        q = dict(query)
        q["page"] = [str(p)]
        q["per_page"] = [str(per_page)]
        qs = "&".join("%s=%s" % (k, v[0]) for k, v in sorted(q.items()))
        return "%s%s?%s" % (base_url, path, qs)
    parts = []
    if page < last_page:
        parts.append('<%s>; rel="next"' % url(page + 1))
        parts.append('<%s>; rel="last"' % url(last_page))
    if page > 1:
        parts.append('<%s>; rel="prev"' % url(page - 1))
        parts.append('<%s>; rel="first"' % url(1))
    return ", ".join(parts) if parts else None

# ---------------------------------------------------------------------------
# REST v3 handlers (each returns (status, body_obj_or_None, extra_headers))
# ---------------------------------------------------------------------------

def rest_create_repo(body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    name = body.get("name")
    if not isinstance(name, str) or not name or "/" in name:
        return 422, {"message": "Invalid repository name"}, {}
    with STORE.lock:
        existing = STORE.get_repo(VIEWER_LOGIN, name)
        if existing is not None:
            return 422, {"message": "Repository already exists"}, {}
        repo = STORE.create_repo(VIEWER_LOGIN, name,
                                 bool(body.get("private", False)),
                                 body.get("description") or "")
    return 201, repo_json(repo), {}

def rest_list_user_repos(query, base_url, path):
    with STORE.lock:
        repos = STORE.viewer_repos()
    items, per_page, page, total = paginate([repo_json(r) for r in repos], query)
    headers = {}
    link = link_header(base_url, path, query, per_page, page, total)
    if link:
        headers["Link"] = link
    return 200, items, headers

def rest_get_repo(owner, name):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
    if repo is None:
        return 404, {"message": "Not Found"}, {}
    return 200, repo_json(repo), {}

def rest_patch_repo(owner, name, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        if "description" in body:
            repo.description = body["description"] or ""
        if "private" in body:
            repo.private = bool(body["private"])
        repo.updated_at = now_iso()
        return 200, repo_json(repo), {}

def rest_delete_repo(owner, name):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        STORE.delete_repo(owner, name)
    return 204, None, {}

def rest_list_branches(owner, name):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        out = []
        for refname in sorted(repo.refs):
            if refname.startswith("refs/heads/"):
                branch = refname[len("refs/heads/"):]
                out.append({"name": branch,
                            "commit": {"sha": repo.refs[refname]},
                            "protected": False})
        return 200, out, {}

def rest_get_branch(owner, name, branch):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        oid = repo.refs.get("refs/heads/" + branch)
        if oid is None:
            return 404, {"message": "Branch not found"}, {}
        return 200, {"name": branch, "commit": {"sha": oid},
                     "protected": False}, {}

def rest_list_commits(owner, name, query):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        sha_param = query.get("sha", [None])[0]
        if sha_param:
            tip = repo.resolve_ref(sha_param)
            if tip is None:
                return 404, {"message": "No commit found for SHA: %s" % sha_param}, {}
        else:
            tip = repo.head_oid()
        commits = repo.commit_list(tip)[:30]
        out = []
        for oid in commits:
            obj = repo.objects.get(oid)
            parsed = parse_commit(obj[1])
            out.append({"sha": oid,
                        "commit": {"message": parsed["message"],
                                   "author": {"name": "forge"},
                                   "committer": {"name": "forge"}},
                        "parents": [{"sha": p} for p in parsed["parents"]]})
        return 200, out, {}

def rest_create_ref(owner, name, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    ref = body.get("ref")
    sha = body.get("sha")
    if not isinstance(ref, str) or not ref.startswith("refs/"):
        return 422, {"message": "Invalid ref"}, {}
    if not is_oid(sha):
        return 422, {"message": "Invalid sha"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        if ref in repo.refs:
            return 422, {"message": "Reference already exists"}, {}
        obj = repo.objects.get(sha)
        if obj is None:
            return 422, {"message": "Object does not exist"}, {}
        repo.refs[ref] = sha
        repo._pack_cache.clear()
        return 201, {"ref": ref, "object": {"sha": sha, "type": obj[0]}}, {}

def rest_get_ref(owner, name, ref):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        oid = repo.refs.get(ref)
        if oid is None:
            return 404, {"message": "Reference not found"}, {}
        obj = repo.objects.get(oid)
        return 200, {"ref": ref, "object": {"sha": oid,
                                            "type": obj[0] if obj else "commit"}}, {}

def rest_list_refs(owner, name):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        out = []
        for refname, oid in sorted(repo.refs.items()):
            obj = repo.objects.get(oid)
            out.append({"ref": refname,
                        "object": {"sha": oid,
                                   "type": obj[0] if obj else "commit"}})
        return 200, out, {}

def _contents_ref(repo, query, body_branch):
    ref = query.get("ref", [None])[0] or body_branch
    if ref is None:
        return repo.head_oid()
    return repo.resolve_ref(ref)

def rest_put_contents(owner, name, path, body, query):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    message = body.get("message")
    content_b64 = body.get("content")
    if not isinstance(message, str) or not isinstance(content_b64, str):
        return 422, {"message": "message and content are required"}, {}
    try:
        raw = base64.b64decode(content_b64.encode("ascii"), validate=False)
    except Exception:
        return 422, {"message": "content is not valid base64"}, {}
    branch = body.get("branch") or DEFAULT_BRANCH
    sha_given = body.get("sha")
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        refname = "refs/heads/" + branch
        tip = repo.refs.get(refname)
        if tip is None:
            # a PUT on a branch that does not exist yet branches it from the
            # default branch tip (or starts the repo when it is unborn)
            tip = repo.head_oid()
        filemap = dict(repo.filemap_of(tip)) if tip else {}
        existing = filemap.get(path)
        if existing is not None:
            if sha_given is None or sha_given.lower() != existing[1].lower():
                return 409, {"message": "sha does not match the current blob"}, {}
            status = 200
        else:
            if sha_given is not None:
                return 422, {"message": "sha given for a file that does not exist"}, {}
            status = 201
        blob_oid = repo.put_object("blob", raw)
        filemap[path] = ("100644", blob_oid)
        tree_oid = repo.build_tree(filemap)
        parents = [tip] if tip else []
        commit_oid = repo.commit_files(tree_oid, parents, message)
        repo.refs[refname] = commit_oid
        repo._filemaps[commit_oid] = dict(filemap)
        repo._pack_cache.clear()
        repo.updated_at = now_iso()
        return status, {
            "content": {"name": path.rsplit("/", 1)[-1], "path": path,
                        "sha": blob_oid, "size": len(raw),
                        "encoding": "base64", "type": "file"},
            "commit": {"sha": commit_oid, "message": message},
        }, {}

def rest_get_contents(owner, name, path, query):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        tip = _contents_ref(repo, query, None)
        if tip is None:
            return 404, {"message": "Not Found"}, {}
        filemap = repo.filemap_of(tip)
        if path == "" or path is None:
            return 200, _directory_listing(repo, filemap, ""), {}
        if path in filemap:
            _mode, blob_oid = filemap[path]
            data = repo.objects[blob_oid][1]
            return 200, {
                "type": "file", "encoding": "base64",
                "content": b64e(data), "sha": blob_oid, "size": len(data),
                "name": path.rsplit("/", 1)[-1], "path": path,
            }, {}
        # directory?
        prefix = path.rstrip("/") + "/"
        entries = [p for p in filemap if p.startswith(prefix)]
        if entries:
            return 200, _directory_listing(repo, filemap, prefix), {}
        return 404, {"message": "Not Found"}, {}

def _directory_listing(repo, filemap, prefix):
    """Entries directly under prefix: files and subdirectories."""
    seen_files = {}
    seen_dirs = {}
    for path, (mode, oid) in filemap.items():
        if not path.startswith(prefix):
            continue
        rest = path[len(prefix):]
        if "/" in rest:
            dname = rest.split("/", 1)[0]
            if dname not in seen_dirs:
                # tree oid of that directory
                submap = {p[len(prefix) + len(dname) + 1:]: v
                          for p, v in filemap.items()
                          if p.startswith(prefix + dname + "/")}
                seen_dirs[dname] = repo.build_tree(submap)
        else:
            seen_files[rest] = oid
    out = []
    for dname, tree_oid in sorted(seen_dirs.items()):
        out.append({"type": "dir", "name": dname,
                    "path": prefix + dname, "sha": tree_oid})
    for fname, oid in sorted(seen_files.items()):
        out.append({"type": "file", "name": fname,
                    "path": prefix + fname, "sha": oid})
    return out

def rest_delete_contents(owner, name, path, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    message = body.get("message")
    sha_given = body.get("sha")
    if not isinstance(message, str):
        return 422, {"message": "message is required"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        branch = body.get("branch") or DEFAULT_BRANCH
        refname = "refs/heads/" + branch
        tip = repo.refs.get(refname)
        if tip is None:
            return 404, {"message": "Not Found"}, {}
        filemap = dict(repo.filemap_of(tip))
        existing = filemap.get(path)
        if existing is None:
            return 404, {"message": "Not Found"}, {}
        if sha_given is not None and sha_given.lower() != existing[1].lower():
            return 409, {"message": "sha does not match the current blob"}, {}
        del filemap[path]
        tree_oid = repo.build_tree(filemap)
        commit_oid = repo.commit_files(tree_oid, [tip], message)
        repo.refs[refname] = commit_oid
        repo._filemaps[commit_oid] = dict(filemap)
        repo._pack_cache.clear()
        repo.updated_at = now_iso()
        return 200, {"commit": {"sha": commit_oid, "message": message}}, {}

def rest_create_label(owner, name, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    label = body.get("name")
    color = body.get("color") or "ededed"
    if not isinstance(label, str) or not label:
        return 422, {"message": "label name is required"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        repo.labels[label] = color
        return 201, {"name": label, "color": color}, {}

def rest_list_labels(owner, name):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        return 200, [{"name": n, "color": c} for n, c in sorted(repo.labels.items())], {}

def rest_create_issue(owner, name, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    title = body.get("title")
    if not isinstance(title, str) or not title:
        return 422, {"message": "title is required"}, {}
    labels = body.get("labels") or []
    if not isinstance(labels, list):
        return 422, {"message": "labels must be an array"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        for label in labels:
            if label not in repo.labels:
                return 422, {"message": "Label does not exist"}, {}
        number = repo.next_issue_number
        repo.next_issue_number += 1
        issue = Issue(number, STORE.next_issue_id(), title, body.get("body") or "")
        issue.labels = list(labels)
        repo.issues.append(issue)
        return 201, issue_json(repo, issue), {}

def rest_list_issues(owner, name, query):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        state = query.get("state", ["open"])[0]
        sort = query.get("sort", ["created"])[0]
        direction = query.get("direction", ["desc"])[0]
        items = list(repo.issues)
        if state in ("open", "closed"):
            items = [i for i in items if i.state == state]
        if sort == "created":
            items.sort(key=lambda i: i.number, reverse=(direction == "desc"))
        page_items, _pp, _pg, _t = paginate([issue_json(repo, i) for i in items], query)
        return 200, page_items, {}

def rest_get_issue(owner, name, number):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        issue = next((i for i in repo.issues if i.number == number), None)
        if issue is None:
            return 404, {"message": "Not Found"}, {}
        return 200, issue_json(repo, issue), {}

def rest_patch_issue(owner, name, number, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        issue = next((i for i in repo.issues if i.number == number), None)
        if issue is None:
            return 404, {"message": "Not Found"}, {}
        if "state" in body and body["state"] in ("open", "closed"):
            issue.state = body["state"]
        if "title" in body and isinstance(body["title"], str):
            issue.title = body["title"]
        if "body" in body and isinstance(body["body"], str):
            issue.body = body["body"]
        issue.updated_at = now_iso()
        return 200, issue_json(repo, issue), {}

def rest_create_comment(owner, name, number, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    text = body.get("body")
    if not isinstance(text, str):
        return 422, {"message": "body is required"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        issue = next((i for i in repo.issues if i.number == number), None)
        if issue is None:
            return 404, {"message": "Not Found"}, {}
        comment = Comment(STORE.next_comment_id(), text)
        issue.comments.append(comment)
        return 201, comment_json(repo, issue, comment), {}

def rest_list_comments(owner, name, number):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        issue = next((i for i in repo.issues if i.number == number), None)
        if issue is None:
            return 404, {"message": "Not Found"}, {}
        return 200, [comment_json(repo, issue, c) for c in issue.comments], {}

def rest_create_pull(owner, name, body):
    if not isinstance(body, dict):
        return 400, {"message": "Invalid request body"}, {}
    head = body.get("head")
    base = body.get("base")
    title = body.get("title")
    if not isinstance(head, str) or not isinstance(base, str) or not isinstance(title, str):
        return 422, {"message": "head, base and title are required"}, {}
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        head_tip = repo.refs.get("refs/heads/" + head)
        base_tip = repo.refs.get("refs/heads/" + base)
        if head_tip is None or base_tip is None:
            return 422, {"message": "head or base branch does not exist"}, {}
        for pr in repo.pulls:
            if pr.head == head and pr.base == base and pr.state == "open":
                return 422, {"message": "A pull request already exists for this branch"}, {}
        number = repo.next_pr_number
        repo.next_pr_number += 1
        pr = PullRequest(number, STORE.next_pr_id(), title, body.get("body") or "",
                         head, base, base_tip)
        repo.pulls.append(pr)
        return 201, pull_json(repo, pr), {}

def rest_list_pulls(owner, name, query):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        state = query.get("state", ["open"])[0]
        items = list(repo.pulls)
        if state in ("open", "closed"):
            items = [p for p in items if p.state == state]
        items.sort(key=lambda p: p.number)
        page_items, _pp, _pg, _t = paginate([pull_json(repo, p) for p in items], query)
        return 200, page_items, {}

def rest_get_pull(owner, name, number):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        pr = next((p for p in repo.pulls if p.number == number), None)
        if pr is None:
            return 404, {"message": "Not Found"}, {}
        return 200, pull_json(repo, pr), {}

def rest_list_pull_files(owner, name, number):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        pr = next((p for p in repo.pulls if p.number == number), None)
        if pr is None:
            return 404, {"message": "Not Found"}, {}
        head_tip = repo.ref_tip("refs/heads/" + pr.head)
        files = pr_changed_files(repo, pr.base_sha, head_tip)
        return 200, files, {}

def do_squash_merge(repo, pr):
    """Perform a squash merge. Returns (status, body)."""
    if pr.state != "open":
        return 405, {"message": "Pull request is already closed"}
    if pr_merge_conflict(repo, pr):
        return 405, {"message": "Merge conflict"}
    head_tip = repo.ref_tip("refs/heads/" + pr.head)
    base_tip = repo.ref_tip("refs/heads/" + pr.base)
    if head_tip is None or base_tip is None:
        return 422, {"message": "head or base branch is missing"}
    head_map = repo.filemap_of(head_tip)
    base_map = dict(repo.filemap_of(base_tip))
    changed = pr_changed_files(repo, pr.base_sha, head_tip)
    for entry in changed:
        path = entry["filename"]
        if entry["status"] == "removed":
            base_map.pop(path, None)
        else:
            base_map[path] = head_map[path]
    tree_oid = repo.build_tree(base_map)
    message = "Merge pull request #%d from %s" % (pr.number, pr.head)
    if pr.title:
        message = "%s (#%d)" % (pr.title, pr.number)
    merge_oid = repo.commit_files(tree_oid, [base_tip], message)
    repo.refs["refs/heads/" + pr.base] = merge_oid
    repo._filemaps[merge_oid] = dict(base_map)
    repo._pack_cache.clear()
    pr.state = "closed"
    pr.merged = True
    pr.merged_at = now_iso()
    pr.merge_commit_sha = merge_oid
    pr.updated_at = now_iso()
    repo.updated_at = now_iso()
    return 200, {"sha": merge_oid, "merged": True, "message": message}

def rest_merge_pull(owner, name, number, body):
    with STORE.lock:
        repo = STORE.get_repo(owner, name)
        if repo is None:
            return 404, {"message": "Not Found"}, {}
        pr = next((p for p in repo.pulls if p.number == number), None)
        if pr is None:
            return 404, {"message": "Not Found"}, {}
        status, body = do_squash_merge(repo, pr)
        return status, body, {}

# ---------------------------------------------------------------------------
# GraphQL v4: tokenizer, parser, executor (no library, per the wire)
# ---------------------------------------------------------------------------

class GraphQLError(Exception):
    pass

_TOKEN_RE = re.compile(r"""
    (?P<ws>[ \t\r\n,]+)
  | (?P<comment>\#[^\n]*)
  | (?P<ellipsis>\.\.\.)
  | (?P<punct>[{}\(\)\[\]:!=\$\@])
  | (?P<string>"(?:\\.|[^"\\])*")
  | (?P<float>-?\d+\.\d+(?:[eE][+-]?\d+)?|-?\d+[eE][+-]?\d+)
  | (?P<int>-?\d+)
  | (?P<name>[_A-Za-z][_0-9A-Za-z]*)
""", re.VERBOSE)

def gql_tokenize(text):
    tokens = []
    pos = 0
    n = len(text)
    while pos < n:
        m = _TOKEN_RE.match(text, pos)
        if not m:
            raise GraphQLError("Unexpected character %r in GraphQL document" % text[pos])
        pos = m.end()
        kind = m.lastgroup
        if kind in ("ws", "comment"):
            continue
        tokens.append((kind, m.group()))
    tokens.append(("eof", ""))
    return tokens

class _GqlParser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.i = 0

    def peek(self):
        return self.tokens[self.i]

    def next(self):
        tok = self.tokens[self.i]
        self.i += 1
        return tok

    def expect(self, kind, value=None):
        tok = self.next()
        if tok[0] != kind or (value is not None and tok[1] != value):
            raise GraphQLError("Expected %s %s, got %s" % (kind, value, tok))
        return tok

    def match(self, kind, value=None):
        tok = self.peek()
        if tok[0] == kind and (value is None or tok[1] == value):
            self.i += 1
            return True
        return False

    def parse_document(self):
        definitions = []
        while self.peek()[0] != "eof":
            definitions.append(self.parse_definition())
        return definitions

    def parse_definition(self):
        kind, value = self.peek()
        if kind == "punct" and value == "{":
            return {"kind": "operation", "operation": "query",
                    "name": None, "variables": {}, "selections": self.parse_selections()}
        if kind == "name" and value in ("query", "mutation", "subscription"):
            op = self.next()[1]
            name = None
            if self.peek()[0] == "name":
                name = self.next()[1]
            variables = {}
            if self.peek() == ("punct", "("):
                variables = self.parse_variable_definitions()
            return {"kind": "operation", "operation": op, "name": name,
                    "variables": variables, "selections": self.parse_selections()}
        if kind == "name" and value == "fragment":
            self.next()
            name = self.expect("name")[1]
            self.expect("name", "on")
            type_name = self.expect("name")[1]
            return {"kind": "fragment", "name": name, "type": type_name,
                    "selections": self.parse_selections()}
        raise GraphQLError("Unexpected definition %r" % (value,))

    def parse_variable_definitions(self):
        variables = {}
        self.expect("punct", "(")
        while not self.match("punct", ")"):
            self.expect("punct", "$")
            name = self.expect("name")[1]
            self.expect("punct", ":")
            self.parse_type()
            if self.match("punct", "="):
                variables[name] = self.parse_value()
            else:
                variables[name] = None
        return variables

    def parse_type(self):
        if self.match("punct", "["):
            self.parse_type()
            self.expect("punct", "]")
        else:
            self.expect("name")
        self.match("punct", "!")

    def parse_selections(self):
        self.expect("punct", "{")
        selections = []
        while not self.match("punct", "}"):
            selections.append(self.parse_selection())
        return selections

    def parse_selection(self):
        kind, value = self.peek()
        if kind == "ellipsis" or (kind == "punct" and value == "..."):
            self.next()
            if self.peek()[0] == "name" and self.peek()[1] == "on":
                self.next()
                type_name = self.expect("name")[1]
                return {"kind": "inline", "type": type_name,
                        "selections": self.parse_selections()}
            name = self.expect("name")[1]
            return {"kind": "spread", "name": name}
        name = self.expect("name")[1]
        alias = None
        if self.match("punct", ":"):
            alias = name
            name = self.expect("name")[1]
        args = {}
        if self.peek() == ("punct", "("):
            args = self.parse_arguments()
        selections = None
        if self.peek() == ("punct", "{"):
            selections = self.parse_selections()
        return {"kind": "field", "name": name, "alias": alias or name,
                "args": args, "selections": selections}

    def parse_arguments(self):
        args = {}
        self.expect("punct", "(")
        while not self.match("punct", ")"):
            name = self.expect("name")[1]
            self.expect("punct", ":")
            args[name] = self.parse_value()
        return args

    def parse_value(self):
        kind, value = self.next()
        if kind == "punct" and value == "$":
            return {"$var": self.expect("name")[1]}
        if kind == "punct" and value == "[":
            items = []
            while not self.match("punct", "]"):
                items.append(self.parse_value())
            return items
        if kind == "punct" and value == "{":
            obj = {}
            while not self.match("punct", "}"):
                name = self.expect("name")[1]
                self.expect("punct", ":")
                obj[name] = self.parse_value()
            return obj
        if kind == "string":
            return json.loads(value)
        if kind == "int":
            return int(value)
        if kind == "float":
            return float(value)
        if kind == "name":
            if value == "true":
                return True
            if value == "false":
                return False
            if value == "null":
                return None
            return {"$enum": value}
        raise GraphQLError("Unexpected value %r" % (value,))

def gql_value(node, variables):
    """Resolve a parsed value: substitute variables, unwrap enums."""
    if isinstance(node, dict):
        if "$var" in node:
            return variables.get(node["$var"])
        if "$enum" in node:
            return node["$enum"]
        return {k: gql_value(v, variables) for k, v in node.items()}
    if isinstance(node, list):
        return [gql_value(v, variables) for v in node]
    return node

# --- schema surface ----------------------------------------------------------

GQL_TYPES = {
    "Query": {"kind": "OBJECT", "fields": [
        "viewer", "repository", "node", "__type", "__schema",
        "createIssue", "closeIssue", "createPullRequest", "mergePullRequest",
        "addComment"]},
    "User": {"kind": "OBJECT", "fields": ["id", "login", "name", "email"]},
    "Repository": {"kind": "OBJECT", "fields": [
        "id", "databaseId", "name", "nameWithOwner", "owner", "defaultBranchRef",
        "viewerPermission", "hasIssuesEnabled", "description", "issue", "issues",
        "pullRequests", "pullRequest", "createdAt", "updatedAt", "url"]},
    "Issue": {"kind": "OBJECT", "fields": [
        "id", "number", "title", "state", "body", "createdAt", "updatedAt",
        "author", "labels", "url"]},
    "PullRequest": {"kind": "OBJECT", "fields": [
        "id", "number", "title", "body", "state", "merged", "mergeable",
        "headRefName", "baseRefName", "headRefOid", "baseRefOid", "files",
        "createdAt", "updatedAt", "author"]},
    "IssueConnection": {"kind": "OBJECT", "fields": ["nodes", "edges", "pageInfo", "totalCount"]},
    "PullRequestConnection": {"kind": "OBJECT", "fields": ["nodes", "edges", "pageInfo", "totalCount"]},
    "PullRequestChangedFileConnection": {"kind": "OBJECT", "fields": ["nodes", "edges", "pageInfo", "totalCount"]},
    "PullRequestChangedFile": {"kind": "OBJECT", "fields": ["path", "additions", "deletions", "changes", "status"]},
    "Ref": {"kind": "OBJECT", "fields": ["name", "target"]},
    "Label": {"kind": "OBJECT", "fields": ["id", "name", "color"]},
    "__Type": {"kind": "OBJECT", "fields": ["name", "kind", "fields", "enumValues", "description"]},
    "__Field": {"kind": "OBJECT", "fields": ["name", "description", "type", "args"]},
    "__EnumValue": {"kind": "OBJECT", "fields": ["name", "description"]},
    "SearchType": {"kind": "ENUM", "enumValues": ["ISSUE", "COMMIT", "DISCUSSION", "MILESTONE", "ORGANIZATION", "PROJECT", "REPOSITORY", "USER"]},
    "IssueState": {"kind": "ENUM", "enumValues": ["OPEN", "CLOSED"]},
    "PullRequestState": {"kind": "ENUM", "enumValues": ["OPEN", "CLOSED", "MERGED"]},
    "MergeableState": {"kind": "ENUM", "enumValues": ["MERGEABLE", "CONFLICTING", "UNKNOWN"]},
    "PullRequestMergeMethod": {"kind": "ENUM", "enumValues": ["MERGE", "SQUASH", "REBASE"]},
    "RepositoryPermission": {"kind": "ENUM", "enumValues": ["ADMIN", "MAINTAIN", "WRITE", "TRIAGE", "READ"]},
    "IssueOrderField": {"kind": "ENUM", "enumValues": ["CREATED_AT", "UPDATED_AT", "COMMENTS"]},
    "OrderDirection": {"kind": "ENUM", "enumValues": ["ASC", "DESC"]},
}

def _type_fields(type_name):
    info = GQL_TYPES.get(type_name)
    if info is None:
        return None
    return info.get("fields", [])

def _check_field(type_name, field_name):
    if field_name == "__typename":
        return
    fields = _type_fields(type_name)
    if fields is None:
        raise GraphQLError('Cannot query field "%s" on type "%s".' % (field_name, type_name))
    if field_name not in fields:
        raise GraphQLError('Cannot query field "%s" on type "%s".' % (field_name, type_name))

# --- executor ----------------------------------------------------------------

class _Executor:
    def __init__(self, variables):
        self.variables = variables or {}
        self.fragments = {}

    def execute(self, definitions, operation_name):
        operations = [d for d in definitions if d["kind"] == "operation"]
        self.fragments = {d["name"]: d for d in definitions if d["kind"] == "fragment"}
        operation = None
        if operation_name:
            for op in operations:
                if op.get("name") == operation_name:
                    operation = op
                    break
            if operation is None:
                raise GraphQLError('Unknown operation named "%s".' % operation_name)
        else:
            if not operations:
                raise GraphQLError("No operation in document")
            operation = operations[0]
        if operation["operation"] == "mutation":
            return self._resolve_selections(operation["selections"], ("Query", None))
        return self._resolve_selections(operation["selections"], ("Query", None))

    def _resolve_selections(self, selections, obj):
        type_name, value = obj
        out = {}
        for sel in selections:
            if sel["kind"] == "spread":
                frag = self.fragments.get(sel["name"])
                if frag is None:
                    raise GraphQLError('Unknown fragment "%s".' % sel["name"])
                if frag["type"] != type_name and type_name != "Query":
                    continue
                out.update(self._resolve_selections(frag["selections"], obj))
            elif sel["kind"] == "inline":
                if sel["type"] != type_name:
                    continue
                out.update(self._resolve_selections(sel["selections"], obj))
            else:
                field = sel["name"]
                _check_field(type_name, field)
                args = {k: gql_value(v, self.variables) for k, v in sel["args"].items()}
                resolved = self._resolve_field(type_name, value, field, args, sel)
                out[sel["alias"]] = resolved
        return out

    def _resolve_field(self, type_name, value, field, args, sel):
        if field == "__typename":
            return type_name
        if type_name == "Query":
            return self._query_field(field, args, sel)
        if type_name == "User":
            return self._scalar_field(value, field)
        if type_name == "Repository":
            return self._repository_field(value, field, args, sel)
        if type_name == "Issue":
            return self._issue_field(value, field, args, sel)
        if type_name == "PullRequest":
            return self._pr_field(value, field, args, sel)
        if type_name in ("IssueConnection", "PullRequestConnection",
                         "PullRequestChangedFileConnection"):
            return self._connection_field(value, field, args, sel)
        if type_name == "PullRequestChangedFile":
            return value.get(field)
        if type_name == "Ref":
            return value.get(field)
        if type_name == "Label":
            return value.get(field)
        if type_name == "__Type":
            return self._introspection_field(value, field, args, sel)
        if type_name == "__Field":
            return value.get(field)
        if type_name == "__EnumValue":
            return value.get(field)
        raise GraphQLError('Cannot query field "%s" on type "%s".' % (field, type_name))

    def _scalar_field(self, value, field):
        if isinstance(value, dict):
            return value.get(field)
        return None

    def _query_field(self, field, args, sel):
        if field == "viewer":
            user = {"login": VIEWER_LOGIN, "id": gid("user", VIEWER_LOGIN),
                    "name": VIEWER_NAME, "email": VIEWER_EMAIL}
            return self._resolve_selections(sel["selections"] or [], ("User", user)) if sel["selections"] else user
        if field == "repository":
            owner = args.get("owner")
            name = args.get("name")
            with STORE.lock:
                repo = STORE.get_repo(owner, name)
            if repo is None:
                return None
            return self._resolve_selections(sel["selections"] or [], ("Repository", repo)) if sel["selections"] else repo
        if field == "node":
            node = self._resolve_node(args.get("id"))
            if node is None:
                return None
            return self._resolve_selections(sel["selections"] or [], node) if sel["selections"] else node
        if field == "__type":
            name = args.get("name")
            info = GQL_TYPES.get(name)
            if info is None:
                return None
            type_obj = {"name": name, "kind": info["kind"], "_info": info}
            return self._resolve_selections(sel["selections"] or [], ("__Type", type_obj)) if sel["selections"] else type_obj
        if field == "__schema":
            return {"queryType": {"name": "Query"}}
        if field in ("createIssue", "closeIssue", "createPullRequest",
                     "mergePullRequest", "addComment"):
            return self._mutation(field, args, sel)
        raise GraphQLError('Cannot query field "%s" on type "Query".' % field)

    def _resolve_node(self, global_id):
        if not isinstance(global_id, str):
            return None
        parts = ungid(global_id)
        if parts is None:
            return None
        kind = parts[0]
        if kind == "repo" and len(parts) == 3:
            with STORE.lock:
                repo = STORE.get_repo(parts[1], parts[2])
            return ("Repository", repo) if repo is not None else None
        if kind == "issue" and len(parts) == 4:
            with STORE.lock:
                repo = STORE.get_repo(parts[1], parts[2])
                issue = next((i for i in repo.issues if i.number == int(parts[3])), None) if repo else None
            return ("Issue", (repo, issue)) if issue is not None else None
        if kind == "pr" and len(parts) == 4:
            with STORE.lock:
                repo = STORE.get_repo(parts[1], parts[2])
                pr = next((p for p in repo.pulls if p.number == int(parts[3])), None) if repo else None
            return ("PullRequest", (repo, pr)) if pr is not None else None
        if kind == "user" and len(parts) == 2:
            return ("User", {"login": VIEWER_LOGIN, "id": global_id,
                             "name": VIEWER_NAME, "email": VIEWER_EMAIL})
        return None

    def _repository_field(self, repo, field, args, sel):
        if field == "id":
            return gid("repo", repo.owner, repo.name)
        if field == "databaseId":
            return repo.database_id
        if field == "name":
            return repo.name
        if field == "nameWithOwner":
            return "%s/%s" % (repo.owner, repo.name)
        if field == "owner":
            user = {"login": repo.owner, "id": gid("user", repo.owner),
                    "name": VIEWER_NAME if repo.owner == VIEWER_LOGIN else repo.owner,
                    "email": VIEWER_EMAIL}
            return self._resolve_selections(sel["selections"] or [], ("User", user)) if sel["selections"] else user
        if field == "defaultBranchRef":
            tip = repo.refs.get("refs/heads/" + repo.default_branch)
            if tip is None:
                return None
            ref = {"name": repo.default_branch}
            return self._resolve_selections(sel["selections"] or [], ("Ref", ref)) if sel["selections"] else ref
        if field == "viewerPermission":
            return "ADMIN"
        if field == "hasIssuesEnabled":
            return True
        if field == "description":
            return repo.description
        if field == "createdAt":
            return repo.created_at
        if field == "updatedAt":
            return repo.updated_at
        if field == "url":
            return "https://example.invalid/%s/%s" % (repo.owner, repo.name)
        if field == "issue":
            number = args.get("number")
            with STORE.lock:
                issue = next((i for i in repo.issues if i.number == number), None)
            if issue is None:
                return None
            return self._resolve_selections(sel["selections"] or [], ("Issue", (repo, issue))) if sel["selections"] else issue
        if field == "issues":
            return self._issues_connection(repo, args, sel)
        if field == "pullRequests":
            return self._prs_connection(repo, args, sel)
        if field == "pullRequest":
            number = args.get("number")
            with STORE.lock:
                pr = next((p for p in repo.pulls if p.number == number), None)
            if pr is None:
                return None
            return self._resolve_selections(sel["selections"] or [], ("PullRequest", (repo, pr))) if sel["selections"] else pr
        return None

    def _issues_connection(self, repo, args, sel):
        with STORE.lock:
            items = list(repo.issues)
        states = args.get("states")
        if states:
            wanted = set(s.upper() for s in states)
            items = [i for i in items if i.state.upper() in wanted]
        order_by = args.get("orderBy") or {}
        direction = (order_by.get("direction") or "ASC").upper()
        items.sort(key=lambda i: i.number, reverse=(direction == "DESC"))
        page_items, page_info = self._page(items, args)
        conn = {"_kind": "issue", "_repo": repo, "_items": page_items,
                "_pageInfo": page_info, "_total": len(items)}
        return self._resolve_selections(sel["selections"] or [], ("IssueConnection", conn)) if sel["selections"] else conn

    def _prs_connection(self, repo, args, sel):
        with STORE.lock:
            items = list(repo.pulls)
        items.sort(key=lambda p: p.number)
        page_items, page_info = self._page(items, args)
        conn = {"_kind": "pr", "_repo": repo, "_items": page_items,
                "_pageInfo": page_info, "_total": len(items)}
        return self._resolve_selections(sel["selections"] or [], ("PullRequestConnection", conn)) if sel["selections"] else conn

    def _page(self, items, args):
        """Apply first/after cursor pagination. Returns (page_items, page_info)."""
        after = args.get("after")
        start = 0
        if after:
            try:
                raw = b64d(after).decode("utf-8")
                _kind, num = raw.split(":")
                num = int(num)
                for idx, item in enumerate(items):
                    if item.number == num:
                        start = idx + 1
                        break
            except Exception:
                pass
        first = args.get("first")
        if isinstance(first, int) and first >= 0:
            page = items[start:start + first]
            has_next = start + first < len(items)
        else:
            page = items[start:]
            has_next = False
        end_cursor = None
        if page:
            end_cursor = b64e(("cursor:%d" % page[-1].number).encode("utf-8"))
        return page, {"hasNextPage": has_next, "endCursor": end_cursor}

    def _connection_field(self, conn, field, args, sel):
        if field == "nodes":
            kind = conn.get("_kind")
            repo = conn.get("_repo")
            out = []
            for item in conn.get("_items", []):
                if kind == "issue":
                    obj = ("Issue", (repo, item))
                elif kind == "pr":
                    obj = ("PullRequest", (repo, item))
                elif kind == "file":
                    obj = ("PullRequestChangedFile", item)
                else:
                    obj = ("Issue", (repo, item))
                if sel["selections"]:
                    out.append(self._resolve_selections(sel["selections"], obj))
                else:
                    out.append(item)
            return out
        if field == "edges":
            kind = conn.get("_kind")
            repo = conn.get("_repo")
            out = []
            for item in conn.get("_items", []):
                if kind == "issue":
                    obj = ("Issue", (repo, item))
                elif kind == "pr":
                    obj = ("PullRequest", (repo, item))
                elif kind == "file":
                    obj = ("PullRequestChangedFile", item)
                else:
                    obj = ("Issue", (repo, item))
                node = self._resolve_selections(sel["selections"] or [], obj) if sel["selections"] else item
                out.append({"node": node,
                            "cursor": b64e(("cursor:%d" % item.number).encode("utf-8")) if hasattr(item, "number") else None})
            return out
        if field == "pageInfo":
            info = conn.get("_pageInfo", {})
            if sel["selections"]:
                return {s["alias"]: info.get(s["name"]) for s in sel["selections"] if s["kind"] == "field"}
            return info
        if field == "totalCount":
            return conn.get("_total")
        return None

    def _issue_field(self, pair, field, args, sel):
        repo, issue = pair
        if field == "id":
            return gid("issue", repo.owner, repo.name, issue.number)
        if field == "number":
            return issue.number
        if field == "title":
            return issue.title
        if field == "state":
            return issue.state.upper()
        if field == "body":
            return issue.body
        if field == "createdAt":
            return issue.created_at
        if field == "updatedAt":
            return issue.updated_at
        if field == "author":
            user = {"login": VIEWER_LOGIN, "id": gid("user", VIEWER_LOGIN),
                    "name": VIEWER_NAME, "email": VIEWER_EMAIL}
            return self._resolve_selections(sel["selections"] or [], ("User", user)) if sel["selections"] else user
        if field == "labels":
            nodes = [{"name": n, "color": repo.labels.get(n, "ededed"), "id": gid("label", repo.owner, repo.name, n)}
                     for n in issue.labels]
            return {"nodes": nodes}
        if field == "url":
            return "https://example.invalid/%s/%s/issues/%d" % (repo.owner, repo.name, issue.number)
        return None

    def _pr_field(self, pair, field, args, sel):
        repo, pr = pair
        if field == "id":
            return gid("pr", repo.owner, repo.name, pr.number)
        if field == "number":
            return pr.number
        if field == "title":
            return pr.title
        if field == "body":
            return pr.body
        if field == "state":
            if pr.merged:
                return "MERGED"
            return pr.state.upper()
        if field == "merged":
            return pr.merged
        if field == "mergeable":
            if pr.state != "open":
                return "UNKNOWN"
            return "CONFLICTING" if pr_merge_conflict(repo, pr) else "MERGEABLE"
        if field == "headRefName":
            return pr.head
        if field == "baseRefName":
            return pr.base
        if field == "headRefOid":
            return repo.ref_tip("refs/heads/" + pr.head) or ZERO_OID
        if field == "baseRefOid":
            return repo.ref_tip("refs/heads/" + pr.base) or ZERO_OID
        if field == "createdAt":
            return pr.created_at
        if field == "updatedAt":
            return pr.updated_at
        if field == "author":
            user = {"login": VIEWER_LOGIN, "id": gid("user", VIEWER_LOGIN),
                    "name": VIEWER_NAME, "email": VIEWER_EMAIL}
            return self._resolve_selections(sel["selections"] or [], ("User", user)) if sel["selections"] else user
        if field == "files":
            head_tip = repo.ref_tip("refs/heads/" + pr.head)
            files = pr_changed_files(repo, pr.base_sha, head_tip)
            nodes = [{"path": f["filename"], "additions": f["additions"],
                      "deletions": f["deletions"], "changes": f["changes"],
                      "status": f["status"]} for f in files]
            first = args.get("first")
            if isinstance(first, int):
                nodes = nodes[:first]
            conn = {"_kind": "file", "_repo": repo, "_items": nodes,
                    "_pageInfo": {"hasNextPage": False, "endCursor": None},
                    "_total": len(nodes)}
            return self._resolve_selections(sel["selections"] or [], ("PullRequestChangedFileConnection", conn)) if sel["selections"] else conn
        return None

    def _introspection_field(self, type_obj, field, args, sel):
        info = type_obj.get("_info", {})
        if field == "name":
            return type_obj.get("name")
        if field == "kind":
            return info.get("kind")
        if field == "description":
            return None
        if field == "fields":
            fields = info.get("fields")
            if fields is None:
                return None
            nodes = [{"name": f} for f in fields]
            if sel["selections"]:
                return [self._resolve_selections(sel["selections"], ("__Field", n)) for n in nodes]
            return nodes
        if field == "enumValues":
            values = info.get("enumValues")
            if values is None:
                return None
            nodes = [{"name": v} for v in values]
            if sel["selections"]:
                return [self._resolve_selections(sel["selections"], ("__EnumValue", n)) for n in nodes]
            return nodes
        return None

    def _mutation(self, field, args, sel):
        if field == "createIssue":
            return self._m_create_issue(args, sel)
        if field == "closeIssue":
            return self._m_close_issue(args, sel)
        if field == "createPullRequest":
            return self._m_create_pr(args, sel)
        if field == "mergePullRequest":
            return self._m_merge_pr(args, sel)
        if field == "addComment":
            return self._m_add_comment(args, sel)
        raise GraphQLError('Cannot query field "%s" on type "Query".' % field)

    def _m_create_issue(self, args, sel):
        inp = args.get("input") or {}
        parts = ungid(inp.get("repositoryId") or "")
        if not parts or parts[0] != "repo" or len(parts) != 3:
            raise GraphQLError("createIssue: unknown repositoryId")
        with STORE.lock:
            repo = STORE.get_repo(parts[1], parts[2])
            if repo is None:
                raise GraphQLError("createIssue: repository not found")
            number = repo.next_issue_number
            repo.next_issue_number += 1
            issue = Issue(number, STORE.next_issue_id(), inp.get("title") or "",
                          inp.get("body") or "")
            repo.issues.append(issue)
        payload = {"issue": (repo, issue)}
        return self._resolve_selections(sel["selections"] or [], ("_CreateIssuePayload", payload)) if sel["selections"] else payload

    def _m_close_issue(self, args, sel):
        inp = args.get("input") or {}
        parts = ungid(inp.get("issueId") or "")
        if not parts or parts[0] != "issue" or len(parts) != 4:
            raise GraphQLError("closeIssue: unknown issueId")
        with STORE.lock:
            repo = STORE.get_repo(parts[1], parts[2])
            issue = next((i for i in repo.issues if i.number == int(parts[3])), None) if repo else None
            if issue is None:
                raise GraphQLError("closeIssue: issue not found")
            issue.state = "closed"
            issue.updated_at = now_iso()
        payload = {"issue": (repo, issue)}
        return self._resolve_selections(sel["selections"] or [], ("_CloseIssuePayload", payload)) if sel["selections"] else payload

    def _m_create_pr(self, args, sel):
        inp = args.get("input") or {}
        parts = ungid(inp.get("repositoryId") or "")
        if not parts or parts[0] != "repo" or len(parts) != 3:
            raise GraphQLError("createPullRequest: unknown repositoryId")
        with STORE.lock:
            repo = STORE.get_repo(parts[1], parts[2])
            if repo is None:
                raise GraphQLError("createPullRequest: repository not found")
            head = inp.get("headRefName")
            base = inp.get("baseRefName")
            head_tip = repo.refs.get("refs/heads/" + (head or ""))
            base_tip = repo.refs.get("refs/heads/" + (base or ""))
            if head_tip is None or base_tip is None:
                raise GraphQLError("createPullRequest: head or base branch does not exist")
            for pr in repo.pulls:
                if pr.head == head and pr.base == base and pr.state == "open":
                    raise GraphQLError("createPullRequest: a pull request already exists for this branch")
            number = repo.next_pr_number
            repo.next_pr_number += 1
            pr = PullRequest(number, STORE.next_pr_id(), inp.get("title") or "",
                             "", head, base, base_tip)
            repo.pulls.append(pr)
        payload = {"pullRequest": (repo, pr)}
        return self._resolve_selections(sel["selections"] or [], ("_CreatePrPayload", payload)) if sel["selections"] else payload

    def _m_merge_pr(self, args, sel):
        inp = args.get("input") or {}
        parts = ungid(inp.get("pullRequestId") or "")
        if not parts or parts[0] != "pr" or len(parts) != 4:
            raise GraphQLError("mergePullRequest: unknown pullRequestId")
        with STORE.lock:
            repo = STORE.get_repo(parts[1], parts[2])
            pr = next((p for p in repo.pulls if p.number == int(parts[3])), None) if repo else None
            if pr is None:
                raise GraphQLError("mergePullRequest: pull request not found")
            status, _body = do_squash_merge(repo, pr)
            if status != 200:
                raise GraphQLError("mergePullRequest: %s" % _body.get("message", "merge failed"))
        payload = {"pullRequest": (repo, pr)}
        return self._resolve_selections(sel["selections"] or [], ("_MergePrPayload", payload)) if sel["selections"] else payload

    def _m_add_comment(self, args, sel):
        inp = args.get("input") or {}
        parts = ungid(inp.get("subjectId") or "")
        if not parts or parts[0] != "issue" or len(parts) != 4:
            raise GraphQLError("addComment: unknown subjectId")
        with STORE.lock:
            repo = STORE.get_repo(parts[1], parts[2])
            issue = next((i for i in repo.issues if i.number == int(parts[3])), None) if repo else None
            if issue is None:
                raise GraphQLError("addComment: issue not found")
            comment = Comment(STORE.next_comment_id(), inp.get("body") or "")
            issue.comments.append(comment)
            node = {"id": gid("comment", repo.owner, repo.name, issue.number, comment.id),
                    "body": comment.body}
        payload = {"commentEdge": {"node": node}}
        return self._resolve_selections(sel["selections"] or [], ("_AddCommentPayload", payload)) if sel["selections"] else payload

# mutation payload pseudo-types: their only fields are the named payload keys
_PAYLOAD_FIELDS = {
    "_CreateIssuePayload": ["issue"],
    "_CloseIssuePayload": ["issue"],
    "_CreatePrPayload": ["pullRequest"],
    "_MergePrPayload": ["pullRequest"],
    "_AddCommentPayload": ["commentEdge"],
}

_orig_check_field = _check_field

def _check_field_patched(type_name, field_name):
    if type_name in _PAYLOAD_FIELDS:
        if field_name == "__typename":
            return
        if field_name not in _PAYLOAD_FIELDS[type_name]:
            raise GraphQLError('Cannot query field "%s" on type "%s".' % (field_name, type_name))
        return
    return _orig_check_field(type_name, field_name)

_check_field = _check_field_patched

_orig_resolve_field = _Executor._resolve_field

def _resolve_field_patched(self, type_name, value, field, args, sel):
    if type_name in _PAYLOAD_FIELDS:
        if field == "__typename":
            return type_name
        inner = value.get(field)
        if inner is None:
            return None
        if field == "issue":
            return self._resolve_selections(sel["selections"] or [], ("Issue", inner)) if sel["selections"] else inner
        if field == "pullRequest":
            return self._resolve_selections(sel["selections"] or [], ("PullRequest", inner)) if sel["selections"] else inner
        if field == "commentEdge":
            node = inner.get("node")
            if sel["selections"]:
                out = {}
                for s in sel["selections"]:
                    if s["kind"] == "field" and s["name"] == "node":
                        node_out = {}
                        for ns in (s["selections"] or []):
                            if ns["kind"] == "field":
                                node_out[ns["alias"]] = node.get(ns["name"])
                        out[s["alias"]] = node_out
                return out
            return inner
        return inner
    return _orig_resolve_field(self, type_name, value, field, args, sel)

_Executor._resolve_field = _resolve_field_patched

def graphql_execute_one(operation):
    """operation: dict with query/variables/operationName. Returns a response dict."""
    query = operation.get("query")
    variables = operation.get("variables") or {}
    operation_name = operation.get("operationName")
    if not isinstance(query, str):
        return {"data": None, "errors": [{"message": "query must be a string"}]}
    try:
        definitions = _GqlParser(gql_tokenize(query)).parse_document()
        executor = _Executor(variables)
        data = executor.execute(definitions, operation_name)
        return {"data": data}
    except GraphQLError as err:
        return {"data": None, "errors": [{"message": str(err)}]}
    except Exception as err:  # never leak a stack trace over the wire
        return {"data": None, "errors": [{"message": "internal error: %s" % err}]}

# ---------------------------------------------------------------------------
# MCP (Model Context Protocol, streamable HTTP)
# ---------------------------------------------------------------------------

MCP_TOOLS = [
    {
        "name": "create_repo",
        "description": "Create a repository for the authenticated user.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "name": {"type": "string", "description": "Repository name"},
                "description": {"type": "string", "description": "Repository description"},
                "private": {"type": "boolean", "description": "Whether the repository is private"},
                "owner": {"type": "string", "description": "Owner login (defaults to the authenticated user)"},
            },
            "required": ["name"],
        },
    },
    {
        "name": "get_repo",
        "description": "Get a repository by owner and name.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_issue",
        "description": "Create an issue in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "title": {"type": "string", "description": "Issue title"},
                "body": {"type": "string", "description": "Issue body"},
            },
            "required": ["owner", "repo", "title"],
        },
    },
    {
        "name": "list_issues",
        "description": "List issues in a repository.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "state": {"type": "string", "description": "Issue state: open, closed or all"},
            },
            "required": ["owner", "repo"],
        },
    },
    {
        "name": "create_pull_request",
        "description": "Create a pull request from a head branch into a base branch.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "title": {"type": "string", "description": "Pull request title"},
                "body": {"type": "string", "description": "Pull request body"},
                "head": {"type": "string", "description": "Head branch name"},
                "base": {"type": "string", "description": "Base branch name"},
            },
            "required": ["owner", "repo", "title", "head", "base"],
        },
    },
    {
        "name": "merge_pull_request",
        "description": "Merge a pull request (squash) and close it.",
        "inputSchema": {
            "type": "object",
            "properties": {
                "owner": {"type": "string", "description": "Repository owner login"},
                "repo": {"type": "string", "description": "Repository name"},
                "pull_number": {"type": "integer", "description": "Pull request number"},
            },
            "required": ["owner", "repo", "pull_number"],
        },
    },
]

_MCP_TOOL_MAP = {t["name"]: t for t in MCP_TOOLS}

def _mcp_result(payload):
    text = json.dumps(payload, separators=(",", ":"))
    return {"content": [{"type": "text", "text": text}],
            "structuredContent": payload, "isError": False}

def _mcp_error_result(message):
    return {"content": [{"type": "text", "text": "Error: " + message}],
            "isError": True}

def mcp_call_tool(name, args):
    """Returns (result_dict, jsonrpc_error_dict_or_None)."""
    tool = _MCP_TOOL_MAP.get(name)
    if tool is None:
        return None, {"code": -32602, "message": "Unknown tool: %s" % name}
    if not isinstance(args, dict):
        args = {}
    required = tool["inputSchema"].get("required", [])
    missing = [r for r in required if r not in args or args[r] is None]
    if missing:
        return None, {"code": -32602,
                      "message": "Missing required argument(s): %s" % ", ".join(missing)}
    try:
        if name == "create_repo":
            owner = args.get("owner") or VIEWER_LOGIN
            if owner != VIEWER_LOGIN:
                return _mcp_error_result("cannot create a repository for another owner"), None
            status, body, _h = rest_create_repo(
                {"name": args["name"], "description": args.get("description", ""),
                 "private": args.get("private", False)})
            if status != 201:
                return _mcp_error_result(body.get("message", "create_repo failed")), None
            return _mcp_result(body), None
        if name == "get_repo":
            status, body, _h = rest_get_repo(args["owner"], args["repo"])
            if status != 200:
                return _mcp_error_result(body.get("message", "repository not found")), None
            return _mcp_result(body), None
        if name == "create_issue":
            status, body, _h = rest_create_issue(
                args["owner"], args["repo"],
                {"title": args["title"], "body": args.get("body", "")})
            if status != 201:
                return _mcp_error_result(body.get("message", "create_issue failed")), None
            return _mcp_result(body), None
        if name == "list_issues":
            status, body, _h = rest_list_issues(
                args["owner"], args["repo"],
                {"state": [args.get("state", "open")]})
            if status != 200:
                return _mcp_error_result(body.get("message", "list_issues failed")), None
            return _mcp_result({"issues": body}), None
        if name == "create_pull_request":
            status, body, _h = rest_create_pull(
                args["owner"], args["repo"],
                {"title": args["title"], "body": args.get("body", ""),
                 "head": args["head"], "base": args["base"]})
            if status != 201:
                return _mcp_error_result(body.get("message", "create_pull_request failed")), None
            return _mcp_result(body), None
        if name == "merge_pull_request":
            try:
                number = int(args["pull_number"])
            except (TypeError, ValueError):
                return _mcp_error_result("pull_number must be an integer"), None
            status, body, _h = rest_merge_pull(args["owner"], args["repo"], number, {})
            if status != 200:
                return _mcp_error_result(body.get("message", "merge failed")), None
            with STORE.lock:
                repo = STORE.get_repo(args["owner"], args["repo"])
                pr = next((p for p in repo.pulls if p.number == number), None) if repo else None
            return _mcp_result(pull_json(repo, pr) if pr else body), None
    except Exception as err:
        return _mcp_error_result(str(err)), None
    return _mcp_error_result("unhandled tool"), None

def mcp_handle(body_bytes):
    """Handle one POST /mcp body. Returns (http_status, response_obj_or_None)."""
    try:
        request = json.loads(body_bytes.decode("utf-8"))
    except Exception:
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32700, "message": "Parse error"}}
    if not isinstance(request, dict):
        return 400, {"jsonrpc": "2.0", "id": None,
                     "error": {"code": -32600, "message": "Invalid Request"}}
    method = request.get("method")
    req_id = request.get("id")
    params = request.get("params") or {}
    if not isinstance(params, dict):
        params = {}
    is_notification = "id" not in request
    if method == "server/discover":
        result = {
            "supportedVersions": ["2026-07-28", "2025-11-25", "2025-06-18",
                                  "2025-03-26", "2024-11-05"],
            "capabilities": {"tools": {}},
            "serverInfo": {"name": SERVER_NAME, "version": VERSION},
            "instructions": "A GitHub-compatible forge: repositories, issues, pull requests.",
            "_meta": {"io.modelcontextprotocol/serverInfo":
                      {"name": SERVER_NAME, "version": VERSION}},
        }
        return 200, {"jsonrpc": "2.0", "id": req_id, "result": result}
    if method == "initialize":
        offered = params.get("protocolVersion") or "2025-11-25"
        if not re.match(r"^\d{4}-\d{2}-\d{2}$", str(offered)):
            offered = "2025-11-25"
        return 200, {"jsonrpc": "2.0", "id": req_id, "result": {
            "protocolVersion": offered,
            "capabilities": {"tools": {}},
            "serverInfo": {"name": SERVER_NAME, "version": VERSION}}}
    if method == "notifications/initialized":
        return 202, None
    if method == "tools/list":
        return 200, {"jsonrpc": "2.0", "id": req_id,
                     "result": {"tools": MCP_TOOLS}}
    if method == "tools/call":
        tool_name = params.get("name")
        tool_args = params.get("arguments") or {}
        result, error = mcp_call_tool(tool_name, tool_args)
        if error is not None:
            return 200, {"jsonrpc": "2.0", "id": req_id, "error": error}
        return 200, {"jsonrpc": "2.0", "id": req_id, "result": result}
    if method is None:
        return 400, {"jsonrpc": "2.0", "id": req_id,
                     "error": {"code": -32600, "message": "Invalid Request"}}
    if is_notification:
        return 202, None
    return 200, {"jsonrpc": "2.0", "id": req_id,
                 "error": {"code": -32601, "message": "Method not found: %s" % method}}

# ---------------------------------------------------------------------------
# HTTP server
# ---------------------------------------------------------------------------

def token_ok(handler):
    auth = handler.headers.get("Authorization")
    if not auth or not auth.startswith("Bearer "):
        return False
    token = auth[7:].strip()
    if not token:
        return False
    if SHOP_TOKEN:
        return token == SHOP_TOKEN
    return True

def read_json_body(handler):
    length = handler.headers.get("Content-Length")
    if length is None:
        handler._body_consumed = True
        return {}, None
    try:
        n = int(length)
    except ValueError:
        handler._body_consumed = True
        return None, "bad Content-Length"
    raw = handler.rfile.read(n) if n > 0 else b""
    handler._body_consumed = True
    if not raw:
        return {}, None
    try:
        return json.loads(raw.decode("utf-8")), None
    except Exception:
        return None, "invalid JSON"

class ForgeHandler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"
    server_version = "Forge/1.0"

    def log_message(self, *args):
        pass

    # -- response helpers ----------------------------------------------------
    def _drain_body(self):
        """Consume any unread request body so the next request on this
        keep-alive connection is not parsed from leftover bytes. Called
        from _send before every response when the handler did not read
        the body itself (e.g. an early 401)."""
        self._body_consumed = True
        length = self.headers.get("Content-Length")
        if not length:
            return
        try:
            n = int(length)
        except ValueError:
            return
        if n > 0:
            try:
                self.rfile.read(n)
            except Exception:
                pass

    def _send(self, status, body_bytes, content_type, extra=None):
        if not getattr(self, "_body_consumed", True):
            self._drain_body()
        headers = {"Content-Type": content_type,
                   "Content-Length": str(len(body_bytes)),
                   "X-GitHub-Request-Id": secrets.token_hex(8)}
        if extra:
            headers.update(extra)
        try:
            self.send_response(status)
            for key, value in headers.items():
                self.send_header(key, value)
            self.end_headers()
            if self.command != "HEAD" and body_bytes:
                self.wfile.write(body_bytes)
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True

    def _send_json(self, status, obj, extra=None):
        if obj is None:
            self._send(status, b"", "application/json; charset=utf-8", extra)
            return
        data = (json.dumps(obj, separators=(",", ":")) + "\n").encode("utf-8")
        self._send(status, data, "application/json; charset=utf-8", extra)

    def _send_bytes(self, status, data, content_type, extra=None):
        self._send(status, data, content_type, extra)

    def _unauthorized(self):
        self._send_json(401, {"message": "Requires authentication"})

    # -- dispatch ------------------------------------------------------------
    def do_GET(self):
        self._dispatch("GET")

    def do_POST(self):
        self._dispatch("POST")

    def do_PUT(self):
        self._dispatch("PUT")

    def do_PATCH(self):
        self._dispatch("PATCH")

    def do_DELETE(self):
        self._dispatch("DELETE")

    def _dispatch(self, method):
        self._body_consumed = False
        try:
            split = urlsplit(self.path)
            path = split.path
            query = parse_qs(split.query, keep_blank_values=True)
            if path == "/healthz" and method == "GET":
                self._send_json(200, {"ok": True})
                return
            if path.startswith("/api/v3") or path == "/api/graphql" or path == "/mcp":
                if not token_ok(self):
                    self._unauthorized()
                    return
            elif ".git/" in path or path.endswith(".git"):
                if not token_ok(self):
                    self._unauthorized()
                    return
            base_url = "http://%s" % (self.headers.get("Host") or "127.0.0.1")
            self._route(method, path, query, base_url)
        except Exception as err:
            # never die on one request: answer 500 JSON and stay up
            try:
                self._send_json(500, {"message": "internal error: %s" % err})
            except Exception:
                self.close_connection = True

    def _route(self, method, path, query, base_url):
        # -- git smart HTTP ---------------------------------------------------
        m = re.match(r"^/([^/]+)/([^/]+)\.git/(info/refs|git-upload-pack|git-receive-pack)$", path)
        if m:
            owner, repo_name, service = unquote(m.group(1)), unquote(m.group(2)), m.group(3)
            self._git_route(method, owner, repo_name, service, query)
            return
        # -- GraphQL ----------------------------------------------------------
        if path == "/api/graphql":
            if method != "POST":
                self._send_json(405, {"message": "Method Not Allowed"})
                return
            body, err = read_json_body(self)
            if err is not None:
                self._send_json(400, {"errors": [{"message": "Request body is not valid JSON"}]})
                return
            if isinstance(body, list):
                self._send_json(200, [graphql_execute_one(op) if isinstance(op, dict) else
                                      {"data": None, "errors": [{"message": "operation must be an object"}]}
                                      for op in body])
            elif isinstance(body, dict):
                self._send_json(200, graphql_execute_one(body))
            else:
                self._send_json(400, {"errors": [{"message": "Request body must be an object or array"}]})
            return
        # -- MCP --------------------------------------------------------------
        if path == "/mcp":
            if method == "GET":
                self._send_json(405, {"message": "Method Not Allowed"})
                return
            if method == "DELETE":
                self._send(204, b"", "application/json; charset=utf-8")
                return
            if method != "POST":
                self._send_json(405, {"message": "Method Not Allowed"})
                return
            length = self.headers.get("Content-Length")
            raw = b""
            if length:
                try:
                    raw = self.rfile.read(int(length))
                except ValueError:
                    raw = b""
            self._body_consumed = True
            status, obj = mcp_handle(raw)
            if obj is None:
                self._send(status, b"", "application/json; charset=utf-8")
            else:
                self._send_json(status, obj)
            return
        # -- REST v3 ----------------------------------------------------------
        if path == "/api/v3" or path == "/api/v3/":
            if method != "GET":
                self._send_json(404, {"message": "Not Found"})
                return
            self._send_json(200, {"current_user_url": "/api/v3/user",
                                  "rate_limit_url": "/api/v3/rate_limit"},
                            {"X-OAuth-Scopes": "repo, read:org"})
            return
        if path == "/api/v3/meta" and method == "GET":
            self._send_json(200, {"installed_version": VERSION})
            return
        if path == "/api/v3/user" and method == "GET":
            self._send_json(200, user_json())
            return
        if path == "/api/v3/user/repos":
            if method == "GET":
                status, body, headers = rest_list_user_repos(query, base_url, path)
                self._send_json(status, body, headers)
                return
            if method == "POST":
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                status, out, headers = rest_create_repo(body)
                self._send_json(status, out, headers)
                return
            self._send_json(404, {"message": "Not Found"})
            return
        if path.startswith("/api/v3/repos/"):
            self._rest_repo_route(method, path, query)
            return
        # -- unknown ----------------------------------------------------------
        self._send_json(404, {"message": "Not Found"})

    def _rest_repo_route(self, method, path, query):
        rest = path[len("/api/v3/repos/"):]
        parts = [unquote(p) for p in rest.split("/")]
        if len(parts) < 2:
            self._send_json(404, {"message": "Not Found"})
            return
        owner, name = parts[0], parts[1]
        tail = parts[2:]
        # /repos/{o}/{r}
        if not tail:
            if method == "GET":
                self._send_json(*rest_get_repo(owner, name))
            elif method == "PATCH":
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                self._send_json(*rest_patch_repo(owner, name, body))
            elif method == "DELETE":
                self._send_json(*rest_delete_repo(owner, name))
            else:
                self._send_json(404, {"message": "Not Found"})
            return
        # /repos/{o}/{r}/branches[/{branch}]
        if tail[0] == "branches":
            if len(tail) == 1 and method == "GET":
                self._send_json(*rest_list_branches(owner, name))
            elif len(tail) == 2 and method == "GET":
                self._send_json(*rest_get_branch(owner, name, tail[1]))
            else:
                self._send_json(404, {"message": "Not Found"})
            return
        # /repos/{o}/{r}/commits
        if tail[0] == "commits" and len(tail) == 1 and method == "GET":
            self._send_json(*rest_list_commits(owner, name, query))
            return
        # /repos/{o}/{r}/git/refs[/...]
        if tail[0] == "git" and len(tail) >= 2 and tail[1] == "refs":
            if method == "POST" and len(tail) == 2:
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                self._send_json(*rest_create_ref(owner, name, body))
                return
            if method == "GET":
                if len(tail) == 2:
                    self._send_json(*rest_list_refs(owner, name))
                else:
                    self._send_json(*rest_get_ref(owner, name, "/".join(tail[2:])))
                return
            self._send_json(404, {"message": "Not Found"})
            return
        # /repos/{o}/{r}/contents/{path...}
        if tail[0] == "contents":
            cpath = "/".join(tail[1:])
            if method == "PUT":
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                self._send_json(*rest_put_contents(owner, name, cpath, body, query))
            elif method == "GET":
                self._send_json(*rest_get_contents(owner, name, cpath, query))
            elif method == "DELETE":
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                self._send_json(*rest_delete_contents(owner, name, cpath, body))
            else:
                self._send_json(404, {"message": "Not Found"})
            return
        # /repos/{o}/{r}/labels
        if tail[0] == "labels":
            if method == "POST" and len(tail) == 1:
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                self._send_json(*rest_create_label(owner, name, body))
            elif method == "GET" and len(tail) == 1:
                self._send_json(*rest_list_labels(owner, name))
            else:
                self._send_json(404, {"message": "Not Found"})
            return
        # /repos/{o}/{r}/issues[/{n}[/comments]]
        if tail[0] == "issues":
            if len(tail) == 1:
                if method == "GET":
                    self._send_json(*rest_list_issues(owner, name, query))
                elif method == "POST":
                    body, err = read_json_body(self)
                    if err is not None:
                        self._send_json(400, {"message": "Request body is not valid JSON"})
                        return
                    self._send_json(*rest_create_issue(owner, name, body))
                else:
                    self._send_json(404, {"message": "Not Found"})
                return
            try:
                number = int(tail[1])
            except ValueError:
                self._send_json(404, {"message": "Not Found"})
                return
            if len(tail) == 2:
                if method == "GET":
                    self._send_json(*rest_get_issue(owner, name, number))
                elif method == "PATCH":
                    body, err = read_json_body(self)
                    if err is not None:
                        self._send_json(400, {"message": "Request body is not valid JSON"})
                        return
                    self._send_json(*rest_patch_issue(owner, name, number, body))
                else:
                    self._send_json(404, {"message": "Not Found"})
                return
            if len(tail) == 3 and tail[2] == "comments":
                if method == "GET":
                    self._send_json(*rest_list_comments(owner, name, number))
                elif method == "POST":
                    body, err = read_json_body(self)
                    if err is not None:
                        self._send_json(400, {"message": "Request body is not valid JSON"})
                        return
                    self._send_json(*rest_create_comment(owner, name, number, body))
                else:
                    self._send_json(404, {"message": "Not Found"})
                return
            self._send_json(404, {"message": "Not Found"})
            return
        # /repos/{o}/{r}/pulls[/{n}[/files|merge]]
        if tail[0] == "pulls":
            if len(tail) == 1:
                if method == "GET":
                    self._send_json(*rest_list_pulls(owner, name, query))
                elif method == "POST":
                    body, err = read_json_body(self)
                    if err is not None:
                        self._send_json(400, {"message": "Request body is not valid JSON"})
                        return
                    self._send_json(*rest_create_pull(owner, name, body))
                else:
                    self._send_json(404, {"message": "Not Found"})
                return
            try:
                number = int(tail[1])
            except ValueError:
                self._send_json(404, {"message": "Not Found"})
                return
            if len(tail) == 2 and method == "GET":
                self._send_json(*rest_get_pull(owner, name, number))
                return
            if len(tail) == 3 and tail[2] == "files" and method == "GET":
                self._send_json(*rest_list_pull_files(owner, name, number))
                return
            if len(tail) == 3 and tail[2] == "merge" and method == "PUT":
                body, err = read_json_body(self)
                if err is not None:
                    self._send_json(400, {"message": "Request body is not valid JSON"})
                    return
                self._send_json(*rest_merge_pull(owner, name, number, body))
                return
            self._send_json(404, {"message": "Not Found"})
            return
        self._send_json(404, {"message": "Not Found"})

    def _git_route(self, method, owner, repo_name, service, query):
        with STORE.lock:
            repo = STORE.get_repo(owner, repo_name)
        if repo is None:
            self._send_json(404, {"message": "Not Found"})
            return
        if service == "info/refs":
            if method != "GET":
                self._send_json(405, {"message": "Method Not Allowed"})
                return
            requested = query.get("service", [None])[0]
            if requested not in ("git-upload-pack", "git-receive-pack"):
                self._send_json(400, {"message": "Unknown service"})
                return
            proto = self.headers.get("Git-Protocol", "")
            if requested == "git-upload-pack" and proto == "version=2":
                body = advertisement_v2(repo)
            else:
                body = advertisement_v0(repo, requested)
            ctype = ("application/x-git-upload-pack-advertisement" if requested == "git-upload-pack"
                     else "application/x-git-receive-pack-advertisement")
            self._send_bytes(200, body, ctype)
            return
        if method != "POST":
            self._send_json(405, {"message": "Method Not Allowed"})
            return
        length = self.headers.get("Content-Length")
        raw = b""
        if length:
            try:
                raw = self.rfile.read(int(length))
            except ValueError:
                raw = b""
        self._body_consumed = True
        if service == "git-upload-pack":
            proto = self.headers.get("Git-Protocol", "")
            try:
                if proto == "version=2":
                    command, args = parse_v2_request(raw)
                    if command == "ls-refs":
                        body = ls_refs_response(repo, args)
                    elif command == "fetch":
                        body = v2_fetch_response(repo, args["wants"], args["haves"],
                                                 args["shallow"], args["depth"],
                                                 args.get("done", True))
                    else:
                        self._send_json(400, {"message": "Unknown command"})
                        return
                else:
                    wants, haves, shallow, depth = parse_v0_fetch(raw)
                    body = v0_fetch_response(repo, wants, haves, shallow, depth)
            except ValueError as err:
                self._send_json(400, {"message": "Malformed request: %s" % err})
                return
            self._send_bytes(200, body, "application/x-git-upload-pack-result")
            return
        if service == "git-receive-pack":
            body = handle_receive_pack(repo, raw)
            if body is None:
                self._send_json(400, {"message": "Malformed push request"})
                return
            self._send_bytes(200, body, "application/x-git-receive-pack-result")
            return
        self._send_json(404, {"message": "Not Found"})

# ---------------------------------------------------------------------------
# lifecycle: register with the env, wait for done (starter main.ts contract)
# ---------------------------------------------------------------------------

class ForgeServer(ThreadingHTTPServer):
    daemon_threads = True
    # 50 concurrent clones open 50 connections at once; the default
    # listen backlog of 5 drops SYNs and costs ~1 s retransmits.
    request_queue_size = 128

    def get_request(self):
        sock, addr = super().get_request()
        try:
            # Small request/response pairs on one keep-alive connection
            # otherwise pay the Nagle + delayed-ACK tax (~20-40 ms each);
            # the read/write workloads are thousands of such round trips.
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        return sock, addr

def make_server(host, port):
    server = ForgeServer((host, port), ForgeHandler)
    server.daemon_threads = True
    return server

def _http_json(url, method="GET", body=None, timeout=30):
    data = json.dumps(body).encode("utf-8") if body is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    if data is not None:
        req.add_header("Content-Type", "application/json")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.status, resp.read()
    except urllib.error.HTTPError as err:
        return err.code, err.read()
    except Exception:
        return 0, b""

def _sleep_backoff(attempt):
    time.sleep(min(2.0, 0.25 * (2 ** min(attempt, 8))))

def run_trial(env_url):
    server = make_server("127.0.0.1", 0)
    port = server.server_address[1]
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    sys.stderr.write("[entry] listening on port %d\n" % port)
    sys.stderr.flush()
    attempt = 0
    while True:
        status, _body = _http_json(env_url + "/register", "POST", {"port": port})
        if status in (200, 409):
            break
        if status in (400, 405):
            sys.stderr.write("[entry] register answered HTTP %d; exiting\n" % status)
            server.shutdown()
            sys.exit(1)
        _sleep_backoff(attempt)
        attempt += 1
    sys.stderr.write("[entry] registered; waiting for the env to say done\n")
    sys.stderr.flush()
    attempt = 0
    while True:
        status, body = _http_json(env_url + "/done", "GET")
        if status == 200:
            try:
                if json.loads(body.decode("utf-8")).get("done") is True:
                    break
            except Exception:
                pass
        _sleep_backoff(attempt)
        attempt += 1
    server.shutdown()
    server.server_close()
    sys.stderr.write("[entry] done\n")
    sys.exit(0)

def main():
    env_url = os.environ.get("MAKEFUN_ENV_URL", "").rstrip("/")
    if env_url:
        run_trial(env_url)
        return
    port = int(os.environ.get("FORGE_PORT", "8123"))
    server = make_server("0.0.0.0", port)
    sys.stderr.write("[entry] standalone mode: listening on port %d\n" % port)
    sys.stderr.write("[entry] token: %s\n" % ("set" if SHOP_TOKEN else "unset (any token accepted)"))
    sys.stderr.flush()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass

if __name__ == "__main__":
    main()
