# Scope that the bots must not widen

Author: Benjamin Stanley Frohman. Session kernel re-check: 16 November 2026. Handoff: 23 November 2026.

This version does **not** prove the vanishing conjecture for `n = p²q`. Hypotheses H2 and H3 stay open. The elliptic packaging of R2 is not a closure.

## What the kernel accepted

| Object | Where | Result |
|---|---|---|
| `RCW.R2TwistFibers` | Lean 4.14.0, Mathlib `4bbdccd`, commit `4221808` on the machine that first passed, re-checked from `RCW-Residuals-Lean` | `Built RCW.R2TwistFibers`. `Build completed successfully.` File was 3997 bytes. Declarations: `R2_positive_fiber_no_square`, `R2_negative_fiber_no_square`. |
| `P2qTheorem28` | Lean 4.22.0, Mathlib `79e94a09`, package from Zenodo `p2q-lean-theorem28-2026-11-06.zip` | `Built P2qTheorem28.Theorem28`. `Build completed successfully.` |
| `P2qStructural`, `P2qTheoremD`, `P2qExtensions` | Same Lean 4.22.0 and Mathlib, package `p2q-lean-extensions-2026-11-06.zip` | `Build completed successfully.` One linter warning at `P2qStructural/Basic.lean:116`. |
| Axiom audit | `lake env lean` after those builds | Every named declaration depends only on `propext`, `Classical.choice`, `Quot.sound`. |

The twist-fiber theorem says there is no integer point on the fibers with `5 ≤ r` and `1 ≤ |d| ≤ (r - 3)/2`. That is not Hypothesis R2.

## What was rejected and must not be published as a certificate

- Imports `Mathlib.Data.Int.Basic` and `Mathlib.Tactic.Nlinarith` do not exist at Mathlib `4bbdccd`.
- `linarith` failed on the undoubled gap.
- A blind `sed` rewrite turned the import into `Mathlib.Tactic.Nnnlinarith`.

## What the PDF is

`drafts/p2q-jumps-v1.5.pdf` is 51 pages. Pages 1–23 are the v0.11-review2 paper. The following pages are the 16 November 2026 kernel re-check and the Lean sources. It is not a rewritten proof of the vanishing conjecture.

The logs in `logs/` are the tails captured from those runs, not the full Mathlib trace. The lines that matter are the `Built …` lines, `Build completed successfully.`, and the `#print axioms` output. Do not describe them as a longer log than they are.

## Header rule already on main

Lean modules now open with the copyright block, then the imports, then a `/-!` docstring whose first line is a `#` heading. The authors line is `Authors: Benjamin Stanley Frohman`. Commits do not carry a `Co-authored-by` trailer.
