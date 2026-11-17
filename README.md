# MathRegistry

MathRegistry distributes compiled Lean packages and exposes their verification reports. This repository contains the `mreg` command-line client, a local Model Context Protocol server, protocol schemas and client tests.

## Install mreg

Use the [website installer](https://mathregistry.com/docs/install/) for the current published release. To install this checkout through pip, use Python 3.10 or newer and Git.

```sh
python -m pip install "git+https://github.com/MoteMath/MathRegistry.git"
mreg --help
```

Python 3.14 supplies zstd support through its standard library. Earlier Python versions can use the `zstandard` package or a `zstd` executable on PATH.

## Sign in and install a package

Package downloads require a beta account. You can sign up through the website. Sign in through the browser, then create a Lean project and install a module.

```sh
mreg login
mreg init my-project
cd my-project
mreg add leanprover-community/mathlib4
mreg install Mathlib.Data.Nat.Basic
mreg audit
```

Install Lean and Lake through elan before using the compiled packages. Supported platforms depend on the selected build. See the [client guide](mreg/dist-beta/README-BETA.md) for prerequisites, verification behavior and platform details.

## Contents

- `mreg/mreg.py` is the version 0.6.6 client.
- `mreg/installer/` contains the shell, PowerShell and Python installer templates. The Python template requires release-version and SHA-256 substitution before distribution.
- `mreg/next/` contains the matching client copy and its regression tests.
- `mcp/` contains the local HTTP MCP server and index builder.
- The client guide covers installation, authentication and verification.
- `docs/schemas/` contains the published JSON schemas.
- `decl-chunks/archives/` contains the deterministic archive builder used by the packed-download tests.

The registry protocol is introduced in [PROTOCOL_v0.md](PROTOCOL_v0.md). Per-build manifests and verification reports provide the details for individual packages.

## Local MCP server

Build an index from downloaded build reports, then start the server with a locally chosen access token.

```sh
python mcp/build_index.py build --builds /path/to/build-reports --out /path/to/index
MREG_MCP_TEST_TOKEN=your-local-token python mcp/server.py --index /path/to/index --port 8765
```

The input directory format is documented in `mcp/build_index.py`. Tool definitions are in `docs/tools.json`.

## Tests

```sh
python -m pip install numpy zstandard
python -m unittest discover -s mreg/next -p 'test_*.py'
```

Some tests require POSIX process behavior. Tests requiring the original large Lean graph dataset are skipped when that dataset is unavailable.

## Licensing

Copyright holders retain their rights to the source in this repository. A project-wide open-source license has yet to be selected. Downloaded Lean packages carry their own licenses and notices, which `mreg` preserves during installation.
