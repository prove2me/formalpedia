-- Prove2me | Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_domainRatio_tendsto
-- name    : Catalog.Novelty.KneeDilutionGrid.domainRatio_tendsto
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:11:58.060252+00:00
-- url     : https://prove2.me/theorems/d8f620a1-465b-4f76-938a-85cbd8435ebd
-- title:
--   The domain factor converges to the slope ratio `b_c / b_p`.
-- statement:
--   The domain factor converges to the slope ratio `b_c / b_p`.
--
--   ```lean
--   theorem Catalog.Novelty.KneeDilutionGrid.domainRatio_tendsto{ac bc ap bp : ℝ} (hbp : 0 < bp) :
--       Filter.Tendsto (fun T => domainRatio ac bc ap bp T) Filter.atTop
--         (nhds (bc / bp)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KneeDomainNarrowing.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KneeDomainNarrowing.lean#L174

-- Thm stub generated from Novelty/KneeDomainNarrowing.lean
import Mathlib
import Definitions.Def_Novelty_KneeDomainNarrowing
import Definitions.Def_Novelty_KneeVariableDilution

/-!
# The narrowing domain factor and permanent protection (NET-87, round 31)

This file continues the limited-memory thread `Novelty.KneeDilutionGrid` →
`Novelty.KneeVariableDilution` with the structural mathematics behind the NET-87
verdict **CODE-AT-4096-IS-PROTECTED**.

The measurement.  Sweeping the retention bar over budget grids gave the code
knee chain `{12 @ ctx 512, 16 @ ctx 1024, 32 @ ctx 4096}` (at ctx 4096:
`k = 28` retains `≈0.976`, below the bar, `k = 32` retains `0.986`, above it),
against a prose knee of `40` at ctx 4096.  Two qualitative claims were extracted:

* **acceleration** — `32` exceeds any value extrapolated from the short-context
  increments (`≤ 24`);
* **narrowing** — the code/prose ratio moves from `≈0.75` at short contexts to
  `≈0.80` at 4096, i.e. the domain factor shrinks while code stays cheaper.

We formalise four things.

### 1. What the sweep licenses (`net87_code_knee_bracket`, `net87_fine_grid_needed`)
A fail at `28` and a pass at `32` bracket the knee in `[29, 32]` and *nothing
finer*: there are two nonnegative antitone profiles with identical retention at
every budget outside the open interval `(28, 32)` whose knees are `29` and `32`.
The reported value `k* = 32` is the top of a four-wide bracket.

### 2. Protection is exactly head dominance (`protection_iff_head_dominance`)
"Code is protected at every bar" is not a numerical accident: it holds for all
thresholds simultaneously **iff** the code retention curve dominates the prose
one pointwise.  So a single domain ordering of knees that survives every bar is
an ordering of retention curves, and conversely.

### 3. The narrowing law (`ratio_strictMono`, `ratio_lt_limit`,
`domainRatio_tendsto`, `narrowing_dichotomy`, `protection_permanent`)
Model each domain by an affine knee law `K_d(T) = a_d + b_d · T` in a shared
phase-transition coordinate `T` (`T = 0` at ctx 512, `T = 1` at ctx 4096 for the
measured fit).  Then

* the ratio `r(T) = K_code(T) / K_prose(T)` is strictly increasing exactly when
  `a_c b_p < a_p b_c` — narrowing is a *sign condition*, not a trend;
* narrowing implies `r(T) < b_c / b_p` for **every** `T`: the ratio approaches
  its limit strictly from below and *never reaches parity*;
* `r(T) → b_c / b_p` (`domainRatio_tendsto`), and the gap `K_prose − K_code`
  stays bounded iff `b_c = b_p` iff the limit ratio is `1` (`narrowing_dichotomy`).

Hence the headline: from *ratio increased* **and** *gap increased* between two
contexts it follows that `b_c < b_p`, so `r(T) < b_c/b_p < 1` forever —
`protection_permanent`.  Extrapolating "`0.75 → 0.80 → …→ 1`" is invalid; the
measured pair of ratios alone cannot decide it (`two_ratios_underdetermine_limit`),
the *gap* is the discriminating observable.

The measured numbers fit exactly: `a_c = 12, b_c = 20, a_p = 16, b_p = 24` give
`r(0) = 3/4`, `r(1) = 4/5`, gap `4 → 8` (measured `16 − 12` and `40 − 32`), and
limiting ratio `5/6` (`net87_measured_fit`).  The same fit predicts a prose knee
of `104/5 = 20.8` at ctx 1024 (`net87_prose_prediction_at_1024`) — a falsifiable
next-cycle target.

### 4. Acceleration is a concavity failure (`concave_chain_bound`,
`code_chain_refutes_concavity`)
Any knee law whose per-doubling increments are nonincreasing satisfies
`K j ≤ K 0 + j (K 1 − K 0)`.  With `K 0 = 12`, `K 1 = 16` this caps `K 3` at
`24`; the measured `32` therefore refutes every concave law, which is the exact
content of "P2 confirmed, the acceleration hits code".
-/

open Catalog.Novelty.KneeDilutionGrid

open Finset

/-! ### 1. What a fail/pass pair at 28/32 licenses -/



/-! ### 2. Protection at every bar is head dominance -/



/-! ### 3. Affine knee laws in the phase-transition coordinate -/

theorem Catalog.Novelty.KneeDilutionGrid.domainRatio_tendsto{ac bc ap bp : ℝ} (hbp : 0 < bp) :
    Filter.Tendsto (fun T => domainRatio ac bc ap bp T) Filter.atTop
      (nhds (bc / bp)) := by sorry
