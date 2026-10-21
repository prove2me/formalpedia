-- Prove2me | Theorems.Thm_zero_subgradient_min
-- name    : zero_subgradient_min
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T12:15:15.343666+00:00
-- url     : https://prove2.me/theorems/8ea80a93-bd92-47a3-9d06-5392ec67d79e
-- title:
--   zero subgradient min
-- statement:
--   If the zero vector is a subgradient of f at x, then x is a minimum point of f: the supporting-hyperplane inequality at x with the zero direction gives f y >= f x for every y, so x belongs to the minimum set.

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

theorem zero_subgradient_min {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hg : ShorNonsmooth.AlmostDiff.IsSubgradient f x 0) : x ∈ MinSet f := by sorry
