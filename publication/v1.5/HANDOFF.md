# Handoff to the GitHub Actions bot and the Zenodo bot

Author: Benjamin Stanley Frohman <frohmanbenjamin@gmail.com>
ORCID: 0009-0006-7068-3718
Date of this handoff: 23 November 2026

Nothing in this directory is optional. A bot that publishes, merges, or writes a description must read `SCOPE.md` and `manifest.json` first.

## What the two bots do

1. **Kernel-certificate** (already on this repository and on `RCW-Residuals-Lean`): `.github/workflows/kernel-certificate.yml`. Run it on this branch before merge. It rebuilds, scans for `sorry` / `admit` / `native_decide` / `axiom`, prints axioms, and re-checks each module. Its artifact is `cert-out/`. That run is a new certificate. It does not replace the 16 November 2026 logs in `logs/`.
2. **Zenodo** (this pull request adds `.github/workflows/zenodo-publish.yml`): after this pull request is merged, dispatch that workflow. It creates a new version of concept DOI `10.5281/zenodo.22713135` from the latest record `24180774` (Version 1.3, 12 November 2026). It keeps the inherited files, adds the files listed in `manifest.json`, writes the description in `ZENODO_METADATA.json`, and publishes. If `ZENODO_TOKEN` is missing, it stops and deposits nothing.

Do not merge on a red kernel-certificate run. Do not publish a description that says Hypothesis R2, H2, H3, or the vanishing conjecture is closed.

## Commits the packet refers to

| Repository | Commit on main when this packet was cut |
|---|---|
| `BenFrohman/RCW-Residuals-Lean` | `e97f2ecc0423aeb97cf11237b1a13439b0ee0e98` |
| `BenFrohman/RCW-Version15-Certificates` | `5501ddebc5ad3d361bd2fbfdd348e556361ab828` |
| `BenFrohman/p2q-jumps-lean` | `5b66051c7cb5e376a25f42c856316c0fe533f451` |

The twist-fiber file that first passed `lake build` on the author’s machine is commit `422180805b97610d2849a183c37e9089570fbff2` (3997 bytes). Later commits on `RCW-Residuals-Lean` changed the header, not the proof.

## Where the drafts are

- `drafts/p2q-jumps-v1.5.pdf` — the document to deposit as the new PDF.
- `drafts/p2q-jumps-v0.11-review2.tex` — the paper source that the first 23 pages come from. Zenodo Version 1.3 already has this text under the same name. Do not replace that inherited file. The new PDF has a different name.
- `drafts/p2q-jumps-v0.11.tex` — the earlier source, already on Version 1.3.
- `drafts/kernel-recheck-front.pdf` — the two kernel-recheck pages alone.
- `drafts/RCW-R2TwistFibers-kernel-certificate.pdf` and `drafts/RCW-R2-TwistFibers-Certificate.pdf` — the shorter certificate notes.
- `logs/` — tails of the 16 November 2026 `lake build` and `#print axioms` runs. See `SCOPE.md`.

Copies of the three PDFs are also at `artifacts/chat-2026-11-16/` because the chat client blocked the sandbox download cards. Earlier chats from before this session were not in the workspace, so they are not in this packet.

## License

The paper deposit stays CC BY 4.0, matching Version 1.3. Lean sources stay Apache-2.0, as named in the copyright header and in `LICENSE`.
