-- Prove2me | Theorems.Thm_subgradients_bounded
-- name    : subgradients_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T12:15:02.329145+00:00
-- url     : https://prove2.me/theorems/c7b0066a-57e1-4d56-ad14-e6e3700b02b9
-- title:
--   subgradients bounded
-- statement:
--   Let f be convex and let S be a bounded set. Then there is a constant K > 0 bounding the norm of every subgradient of f at every point of S. The argument is that a subgradient of arbitrarily large norm at a point of S would, by the supporting-hyperplane inequality, produce a point of S at bounded distance with a strictly smaller value of f, contradicting the Lipschitz behaviour of f on the enclosing ball.

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

theorem subgradients_bounded {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : Bornology.IsBounded S) :
    ∃ K : ℝ, 0 < K ∧ ∀ x ∈ S, ∀ v,
      ShorNonsmooth.AlmostDiff.IsSubgradient f x v → ‖v‖ ≤ K := by sorry
