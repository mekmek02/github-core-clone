# github-core-clone

[![make.fun · github-core-clone-01](https://make.fun/badge/github-core-clone-01.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![rank](https://make.fun/badge/github-core-clone-01/mekmek02/github-core-clone/rank.svg)](https://make.fun/bounty/github-core-clone-01/leaderboard?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)
[![reward](https://make.fun/badge/github-core-clone-01/mekmek02/github-core-clone/reward.svg)](https://make.fun/bounty/github-core-clone-01?utm_source=github&utm_medium=readme&utm_campaign=github-core-clone-01)

A single-process GitHub-compatible forge written in pure Python 3.13
standard library, built for the
[make.fun github-core-clone-01 competition](https://make.fun/bounty/github-core-clone-01)
(referral code `dxrvhdam`).

From one process, with its own in-memory store and no outside service, it
serves:

- **Git smart HTTP** — clone and push over `/{owner}/{repo}.git`
  (upload-pack protocol v2 with v0 fallback, receive-pack v0), with real
  git objects: commits, trees, blobs, tags and packfiles (plain objects
  plus OFS/REF delta decoding on receive).
- **REST v3 API** under `/api/v3` — repositories, branches, commits,
  git refs, contents (create/read/update/delete), labels, issues,
  comments, and pull requests (create, list, files, squash merge).
- **GraphQL** at `/api/graphql` — the queries and mutations the `gh` CLI
  and `github-mcp-server` send (viewer, repository, node, issues and
  pullRequests connections with cursor pagination, `__type`, batched
  operations, create/close/merge mutations).
- **MCP tools** at `/mcp` (Streamable HTTP, JSON-RPC 2.0) — `server/discover`,
  `initialize`, `tools/list`, `tools/call` for `create_repo`, `get_repo`,
  `create_issue`, `list_issues`, `create_pull_request`, `merge_pull_request`.

## Run

```sh
python3 main.py
```

Standalone mode listens on `0.0.0.0:8123` (override with `FORGE_PORT`).
Every API call needs a bearer token (`MAKEFUN_SHOP_TOKEN`); when the
token is unset, any non-empty bearer token is accepted. Under the sealed
grader the entry binds an ephemeral port, registers it at
`$MAKEFUN_ENV_URL/register`, and exits when `$MAKEFUN_ENV_URL/done`
reports done.

Health check: `GET /healthz` returns `{"ok": true}`.

## Layout

- `main.py` — the whole forge (git objects, pack protocol, REST, GraphQL, MCP, HTTP server, lifecycle).
- `LICENSE` — MIT.
- `.makefun/owner.json` — make.fun account wallet for ownership checks.
