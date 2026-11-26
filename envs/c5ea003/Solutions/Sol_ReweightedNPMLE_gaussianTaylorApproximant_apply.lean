-- Prove2me | solution 1 for ReweightedNPMLE.gaussianTaylorApproximant_apply
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:13:12.969193+00:00
-- url     : https://prove2.me/submissions/1fdf597c-030f-496c-8461-3215e1b8c144

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

-- Inline helpers preserved from ReweightedNPMLE.GaussianWidth.
section
/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

namespace ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/



theorem truncatedInnerCoeff_spec {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (i : Fin n) (θ : Point d) :
    (∑ ell ∈ Finset.range (L + 1),
      (inner ℝ (x i) θ) ^ ell / ell.factorial) =
      ∑ m, truncatedInnerCoeff L x i m * pointMonomialEval θ m :=
  Classical.choose_spec (truncatedInnerExp_isPointMonomialCombination L (x i)) θ

























end ReweightedNPMLE
end

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

open ReweightedNPMLE







/-! ## The concrete Gaussian Taylor subspace -/
open ReweightedNPMLE in
/-- Coordinate formula for the explicit Taylor approximant. -/
theorem solution {d n : ℕ} (L : ℕ)
    (x : Fin n → Point d) (v₀ : Fin n → ℝ) (θ : Point d) (i : Fin n) :
    gaussianTaylorApproximant L x v₀ θ i =
      Real.exp (-‖θ‖ ^ 2 / 2) *
          (∑ ell ∈ Finset.range (L + 1),
            (inner ℝ (x i) θ) ^ ell / ell.factorial) / v₀ i - 1 := by
  unfold gaussianTaylorApproximant
  simp only [WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul,
    PiLp.toLp_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, gaussianWidthGenerator]
  change (∑ m : MonomialCoord d L,
      (Real.exp (-‖θ‖ ^ 2 / 2) * pointMonomialEval θ m) *
        (truncatedInnerCoeff L x i m / v₀ i)) - 1 = _
  rw [truncatedInnerCoeff_spec L x i θ]
  apply congrArg (fun z ↦ z - 1)
  calc
    ∑ m, (Real.exp (-‖θ‖ ^ 2 / 2) * pointMonomialEval θ m) *
        (truncatedInnerCoeff L x i m / v₀ i) =
        (∑ m, Real.exp (-‖θ‖ ^ 2 / 2) *
          (truncatedInnerCoeff L x i m * pointMonomialEval θ m)) / v₀ i := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro m _
            ring
    _ = Real.exp (-‖θ‖ ^ 2 / 2) *
        (∑ m, truncatedInnerCoeff L x i m * pointMonomialEval θ m) / v₀ i := by
          rw [Finset.mul_sum]
