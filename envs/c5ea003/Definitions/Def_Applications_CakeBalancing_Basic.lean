-- Prove2me | Definitions.Def_Applications_CakeBalancing_Basic
-- name    : Applications_CakeBalancing_Basic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:38:17.43699+00:00
-- url     : https://prove2.me/theorems/21743954-4086-49b2-bc45-180093bb8be9
-- title:
--   Aether Catalog definitions — Applications_CakeBalancing_Basic
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CakeBalancing.Basic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CakeBalancing/Basic.lean by skeleton subtraction
import Mathlib

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

namespace CakeBalancing

variable {n : ℕ}

/-- The weight of the window of `r` consecutive pieces starting at cut `i`,
indices read cyclically. -/
noncomputable def windowSum [NeZero n] (arc : ZMod n → ℝ) (r : ℕ) (i : ZMod n) : ℝ :=
  ∑ j ∈ Finset.range r, arc (i + (j : ZMod n))

/-- The largest window weight. -/
noncomputable def maxWindow [NeZero n] (arc : ZMod n → ℝ) (r : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (windowSum arc r)

/-- The smallest window weight. -/
noncomputable def minWindow [NeZero n] (arc : ZMod n → ℝ) (r : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (windowSum arc r)

/-- The largest single piece. -/
noncomputable def maxArc [NeZero n] (arc : ZMod n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty arc

/-- The smallest single piece. -/
noncomputable def minArc [NeZero n] (arc : ZMod n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty arc

/-- The cake-balancing ratio for windows of length `r`. -/
noncomputable def mu [NeZero n] (arc : ZMod n → ℝ) (r : ℕ) : ℝ :=
  maxWindow arc r / minWindow arc r














/-! ### Examples -/

-- The functionals are well defined for every window length.
-- A concrete `4`-piece equipartition of a circumference-`1` cake has ratio `1`.
end CakeBalancing


