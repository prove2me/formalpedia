-- Prove2me | Theorems.Thm_RademacherComparison_ball_infinite
-- name    : RademacherComparison.ball_infinite
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:41:34.110187+00:00
-- url     : https://prove2.me/theorems/33894600-1e71-4010-9fb4-d76b1c1306b5
-- title:
--   The ball of positive radius is an infinite class, so every bound obtained by
-- statement:
--   The ball of positive radius is an infinite class, so every bound obtained by
--   counting the behaviours of the class on the sample — in particular every VC/Sauer
--   bound and Massart's finite class lemma — is vacuous for it.
--
--   ```lean
--   theorem RademacherComparison.ball_infinite{r : ℝ} (hr : 0 < r) (hn : 0 < n) : (ball n r).Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Comparison.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Comparison.lean#L147

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

theorem RademacherComparison.ball_infinite{r : ℝ} (hr : 0 < r) (hn : 0 < n) : (ball n r).Infinite := by sorry
