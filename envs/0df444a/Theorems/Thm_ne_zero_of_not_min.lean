-- Prove2me | Theorems.Thm_ne_zero_of_not_min
-- name    : ne_zero_of_not_min
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T12:15:05.876355+00:00
-- url     : https://prove2.me/theorems/313f60ea-c0c5-4829-8721-7e751cd932d1
-- title:
--   ne zero of not min
-- statement:
--   If a subgradient of f at x is zero, then x is a minimum point of f. Consequently, at a point that is not a minimum of f, every subgradient is nonzero.

import Mathlib
import Definitions.Def_ShorNonsmooth_Stochastic_StochasticSubgradientMethod
import Definitions.Def_ShorNonsmooth_SubgradMethod_SubgradientMethod
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Filter Topology
open scoped RealInnerProductSpace
open ShorNonsmooth.Stochastic
open ShorNonsmooth.SubgradMethod

theorem ne_zero_of_not_min {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (x gx : EuclideanSpace ℝ (Fin n)) (hg : ShorNonsmooth.AlmostDiff.IsSubgradient f x gx)
    (hx : x ∉ MinSet f) : gx ≠ 0 := by sorry
