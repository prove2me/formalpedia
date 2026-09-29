-- Prove2me | Theorems.Thm_RademacherComparison_vc_bound_eventually_worse
-- name    : RademacherComparison.vc_bound_eventually_worse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:39.935364+00:00
-- url     : https://prove2.me/theorems/e737e86d-14bf-4182-bc2d-71d14b3b2186
-- title:
--   The dimension-dependent (VC-type) bound is eventually worse.
-- statement:
--   **The dimension-dependent (VC-type) bound is eventually worse.**
--   For linear predictors in dimension `d` the VC dimension is `d` (or `d+1`), so a VC-style
--   bound has the shape `c √(d/n)`; the Rademacher margin bound is `W B/√n`.  Whatever the
--   constant `c > 0`, once the dimension exceeds `(W B / c)²` the VC-style bound is strictly
--   larger, i.e. strictly weaker.
--
--   ```lean
--   theorem RademacherComparison.vc_bound_eventually_worse{W B c : ℝ} (hW : 0 < W) (hB : 0 < B) (hc : 0 < c)
--       (hn : 0 < n) {d : ℕ} (hd : (W * B / c) ^ 2 < d) :
--       W * B / Real.sqrt n < c * Real.sqrt ((d : ℝ) / n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Comparison.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Comparison.lean#L170

-- Thm stub generated from Logic/Rademacher/Comparison.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Comparison
/-
# Rademacher complexity beats cardinality (VC) counting on structured classes

Massart's finite class lemma bounds the Rademacher complexity of a class of `N` vectors
by `r √(2 log N)/n`, and VC-type bounds bound `N` (the number of behaviours on the
sample) by a function of the VC dimension.  Both are *counting* bounds and become
vacuous for classes that are infinite on the sample.

This file computes the empirical Rademacher complexity of the Euclidean ball of
radius `r`, i.e. of the class of all vectors of length at most `r`:

  `rad (ball r) = r / √n`   (`rad_ball`),

and shows that this class is infinite (`ball_infinite`), so no cardinality bound
applies to it, while its Rademacher complexity is finite, dimension free, and even
*exactly* computable.  Every subclass of the ball inherits the bound
(`rad_le_of_subset_ball`), which is the abstract form of the margin bound for linear
predictors.

Finally `vc_bound_eventually_worse` records the quantitative comparison: for a class of
linear predictors in dimension `d`, the VC dimension grows with `d`, so any bound of the
shape `c √(d/n)` eventually exceeds the dimension-free Rademacher bound `W B / √n`.

This file is self-contained.
-/

open RademacherComparison

open Finset

variable {n : ℕ}

theorem RademacherComparison.vc_bound_eventually_worse{W B c : ℝ} (hW : 0 < W) (hB : 0 < B) (hc : 0 < c)
    (hn : 0 < n) {d : ℕ} (hd : (W * B / c) ^ 2 < d) :
    W * B / Real.sqrt n < c * Real.sqrt ((d : ℝ) / n) := by sorry
