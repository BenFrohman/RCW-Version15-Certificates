#!/usr/bin/env python3
"""Deposit Version 1.5 as a new Zenodo version of concept 10.5281/zenodo.22713135.

Reads ZENODO_METADATA.json and manifest.json beside this file.
Stops without publishing if the token is missing, the metadata claims something
SCOPE.md forbids, or Zenodo does not return a new draft.
"""
import json
import os
import sys
from pathlib import Path
from urllib.request import Request, urlopen
from urllib.error import HTTPError

ROOT = Path(__file__).resolve().parent
API = "https://zenodo.org/api"
UA = "FrohmanZenodoBot/1.5 (mailto:frohmanbenjamin@gmail.com)"


def call(method, url, token, data=None, raw=None, content_type=None):
    headers = {"Authorization": f"Bearer {token}", "User-Agent": UA}
    body = None
    if data is not None:
        body = json.dumps(data).encode()
        headers["Content-Type"] = "application/json"
    elif raw is not None:
        body = raw
        if content_type:
            headers["Content-Type"] = content_type
    req = Request(url, data=body, headers=headers, method=method)
    try:
        with urlopen(req) as resp:
            payload = resp.read()
            return resp.status, json.loads(payload) if payload else {}
    except HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")
        raise SystemExit(f"{method} {url} failed: {exc.code} {detail[:2000]}")


def main():
    token = os.environ.get("ZENODO_TOKEN", "").strip()
    if not token:
        raise SystemExit("ZENODO_TOKEN is not set. No deposit was made.")
    meta = json.loads((ROOT / "ZENODO_METADATA.json").read_text())
    manifest = json.loads((ROOT / "manifest.json").read_text())
    description = meta["metadata"]["description"]
    for claim in manifest["forbidden_claims"]:
        if claim.lower() in description.lower():
            raise SystemExit(f"refusing to publish: description contains forbidden claim: {claim}")
    previous = meta["previous_record"]
    status, found = call(
        "GET",
        f"{API}/deposit/depositions?q=conceptrecid:22713135&status=published&sort=mostrecent&size=5",
        token,
    )
    if not found:
        dep_id = previous
    else:
        dep_id = str(found[0]["id"])
    _, original = call("POST", f"{API}/deposit/depositions/{dep_id}/actions/newversion", token)
    draft_url = original["links"]["latest_draft"]
    _, draft = call("GET", draft_url, token)
    draft_id = str(draft["id"])
    bucket = draft["links"]["bucket"]
    _, draft = call("PUT", f"{API}/deposit/depositions/{draft_id}", token, data={"metadata": meta["metadata"]})
    for rel in manifest["upload"]:
        path = ROOT / rel
        if not path.is_file():
            raise SystemExit(f"missing upload file: {rel}")
        name = path.name
        call("PUT", f"{bucket}/{name}", token, raw=path.read_bytes(), content_type="application/octet-stream")
        print(f"uploaded {name} ({path.stat().st_size} bytes)")
    if os.environ.get("ZENODO_PUBLISH", "true").lower() != "true":
        print(f"draft left unpublished: deposition {draft_id}")
        return
    _, published = call("POST", f"{API}/deposit/depositions/{draft_id}/actions/publish", token)
    doi = published.get("doi") or published.get("metadata", {}).get("prereserve_doi", {}).get("doi")
    print(f"published deposition {published.get('id')} doi={doi}")


if __name__ == "__main__":
    main()
