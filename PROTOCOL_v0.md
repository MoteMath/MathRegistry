# MathRegistry client protocol

The registry serves package metadata, compiled modules and verification reports over HTTPS. The default endpoint is `https://mathregistry.com`.

## Authentication

`mreg login` uses browser sign-in to obtain a personal API key. The client stores the key in the user's configuration directory and sends it in the `x-mreg-token` header when accessing protected endpoints. Public documentation and sign-in pages can be read without a key.

## Packages and builds

A package identifies a Lean project. A build identifies its compiled output for a particular source revision, Lean toolchain and dependency set. A train groups compatible package builds.

Package manifests describe artifacts and their hashes. Signed manifests and verification reports are checked by the client before installation. The client also checks downloaded artifact hashes and records installed builds in its lock file.

## Verification

The client distinguishes download success, hash integrity and verification policy. `mreg audit` checks signatures, reports and transparency-log consistency. Consult command help for explicit options that change admission policy.

## Schemas

The JSON schemas in `docs/schemas/` describe manifests, signatures, signing keys, packages, trains, lock files, verification reports and transparency-log records. The tool definitions in `docs/tools.json` provide MCP input and output schemas.

The declaration-store layout and named-import command outputs are documented in [NAMED_IMPORT.md](mreg/next/NAMED_IMPORT.md).
