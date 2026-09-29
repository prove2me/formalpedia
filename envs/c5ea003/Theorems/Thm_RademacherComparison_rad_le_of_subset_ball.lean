-- Prove2me | Theorems.Thm_RademacherComparison_rad_le_of_subset_ball
-- name    : RademacherComparison.rad_le_of_subset_ball
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:37.353544+00:00
-- url     : https://prove2.me/theorems/1acaf66c-4a83-49f1-b5f3-78a5b2bcc91b
-- title:
--   Any class contained in the ball of radius `r` obeys the dimension-free bound
-- statement:
--   Any class contained in the ball of radius `r` obeys the dimension-free bound
--   `r/√n`; this is the abstract form of the margin bound for linear predictors.
--
--   ```lean
--   theorem RademacherComparison.rad_le_of_subset_ball{F : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 ≤ r) (hn : 0 < n)
--       (hF : F ⊆ ball n r) : rad F ≤ r / Real.sqrt n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Comparison.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Comparison.lean#L127

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

theorem RademacherComparison.rad_le_of_subset_ball{F : Set (Fin n → ℝ)} {r : ℝ} (hr : 0 ≤ r) (hn : 0 < n)
    (hF : F ⊆ ball n r) : rad F ≤ r / Real.sqrt n := by sorry
