-- Prove2me | solution 1 for ReweightedNPMLE.gaussianFittedSet_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:13:09.695317+00:00
-- url     : https://prove2.me/submissions/7f6a1d79-3908-431d-a37e-da932ad41097

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FittedGeometry
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_abs_gaussianScore_le

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE



























































theorem exp_neg_scoreBound_le_exp_score {d : ℕ} {x θ : Point d} {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) :
    Real.exp (-(T * S + S ^ 2 / 2)) ≤ Real.exp (gaussianScore x θ) := by
  apply Real.exp_le_exp.mpr
  exact neg_le_of_abs_le (abs_gaussianScore_le hT hS hx hθ)



end ReweightedNPMLE
end

/-!
# Compact fitted-value geometry

The infinite-dimensional mixing-law optimization is reduced to the compact
convex hull of the continuous Gaussian evaluation dictionary.  The compact
convex-hull theorem shows this is the actual finite-mixture hull, not merely
its closure, and the Gaussian lower bound keeps it in the positive orthant.
-/

open Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Every point of the closed fitted-value hull inherits the same coordinate
lower bound as the Gaussian dictionary. -/
theorem solution {d n : ℕ}
    (x : Fin n → Point d) (K : Set (Point d))
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ∀ i, ‖x i‖ ≤ T) (hK : ∀ θ ∈ K, ‖θ‖ ≤ S)
    {v : Fin n → ℝ} (hv : v ∈ gaussianFittedSet x K) (i : Fin n) :
    Real.exp (-(T * S + S ^ 2 / 2)) ≤ v i := by
  let lower := Real.exp (-(T * S + S ^ 2 / 2))
  let H : Set (Fin n → ℝ) := {z | lower ≤ z i}
  have hdict : gaussianScoreFeature x '' K ⊆ H := by
    rintro _ ⟨θ, hθK, rfl⟩
    exact exp_neg_scoreBound_le_exp_score hT hS (hx i) (hK θ hθK)
  have hconv : Convex ℝ H := by
    intro a ha b hb p q hp hq hpq
    change lower ≤ (p • a + q • b) i
    change lower ≤ p * a i + q * b i
    calc
      lower = p * lower + q * lower := by rw [← add_mul, hpq, one_mul]
      _ ≤ p * a i + q * b i :=
        add_le_add (mul_le_mul_of_nonneg_left ha hp)
          (mul_le_mul_of_nonneg_left hb hq)
  exact convexHull_min hdict hconv hv
