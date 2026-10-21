-- Prove2me | Theorems.Thm_gap_on_annulus
-- name    : gap_on_annulus
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T12:15:05.658689+00:00
-- url     : https://prove2.me/theorems/8fcd3251-4e82-4e55-b54d-77c7cbd2c8c4
-- title:
--   gap on annulus
-- statement:
--   Let f be convex and let z be a minimum point of f. Then for r > 0 and R >= r there is c > 0 such that f w - f z >= c whenever r <= ||w - z|| <= R. In other words f has a positive gap above its minimum on the annulus at distance at least r from z and within distance R.

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

theorem gap_on_annulus {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ MinSet f)
    (r R : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ w, r ≤ ‖w - z‖ → ‖w - z‖ ≤ R → f w - f z ≥ c := by sorry
