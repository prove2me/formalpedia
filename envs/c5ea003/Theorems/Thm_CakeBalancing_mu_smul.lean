-- Prove2me | Theorems.Thm_CakeBalancing_mu_smul
-- name    : CakeBalancing.mu_smul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:26:13.555042+00:00
-- url     : https://prove2.me/theorems/8383ac77-ef05-40f2-b904-d8b5885f1077
-- title:
--   Scale invariance: rescaling every piece by a positive constant (e.g.
-- statement:
--   **Scale invariance**: rescaling every piece by a positive constant (e.g.
--   changing the circumference) leaves the balancing ratio unchanged.
--
--   ```lean
--   theorem CakeBalancing.mu_smul[NeZero n] (arc : ZMod n → ℝ) {c : ℝ} (hc : 0 < c) (r : ℕ) :
--       mu (fun i => c * arc i) r = mu arc r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/CakeBalancing/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/CakeBalancing/Basic.lean#L186

-- Thm stub generated from Applications/CakeBalancing/Basic.lean
import Mathlib
import Definitions.Def_Applications_CakeBalancing_Basic

/-!
# The cake-balancing ratio functional

Consider a circular cake whose boundary carries finitely many cut points.  When
`n` cuts are present they divide the circle into `n` arcs (the *pieces*).  Fix a
window length `r ≥ 1`.  For each starting position `i` the sum of the `r`
consecutive pieces `i, i+1, …, i+r-1` (indices read cyclically) is a *window
weight*.  The **balancing ratio**

`μ_r = (largest window weight) / (smallest window weight)`

measures how far the current dissection is from perfectly balancing every block
of `r` consecutive pieces.  A dissection is perfectly balanced for windows of
length `r` exactly when `μ_r = 1`.

This file develops the exact, dimension-free algebra of this functional for a
single dissection.  A circular dissection into `n` pieces is modelled by a
positive weight function `arc : ZMod n → ℝ`, the cyclic group `ZMod n`
supplying the wrap-around index arithmetic for free.

The headline structural results are:

* `mu_ge_one` — the ratio is always at least `1`;
* `mu_le_arcRatio` / `mu_le_mu_one` — **aggregation never increases imbalance**:
  the window ratio for any `r ≥ 1` is bounded by the ratio of the single largest
  to the single smallest piece;
* `mu_smul` — the ratio is scale invariant, so the circumference is irrelevant;
* `mu_equipartition` — an equipartition realises the optimal value `1`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  Grouping consecutive pieces should *average out*
local fluctuations, so the imbalance seen through a window of length `r` can
never exceed the raw piece-to-piece imbalance `μ_1 = maxArc / minArc`.  We
conjectured the sharp comparison `μ_r ≤ μ_1` for every `r ≥ 1`, together with
scale invariance and attainment of `1` at the equipartition.

EXPERIMENT (Experimenter).  Each window weight is a sum of `r` pieces, hence
sandwiched between `r · minArc` and `r · maxArc`.  Passing to the extremal
windows and cancelling the common factor `r` yields `μ_r ≤ maxArc / minArc`, and
`μ_1 = maxArc / minArc` because a length-one window is a single piece.

ANALYSIS (Analyst).  The factor `r` cancels *exactly*; the comparison is not an
asymptotic estimate but an identity-driven inequality valid for every finite
dissection.  Positivity of the pieces is the only hypothesis that does real
work (it keeps the denominator away from `0`).

CRITIQUE (Critic).  The results are non-vacuous: the equipartition witnesses
equality in `mu_ge_one`, and two-valued dissections (see the companion file)
witness strict inequality, so neither bound is degenerate.  The boundary case
`r = 0` (empty window) is excluded exactly as the informal statement demands
`r ≥ 1`.
-/

open Finset

open CakeBalancing

variable {n : ℕ}

theorem CakeBalancing.mu_smul[NeZero n] (arc : ZMod n → ℝ) {c : ℝ} (hc : 0 < c) (r : ℕ) :
    mu (fun i => c * arc i) r = mu arc r := by sorry
