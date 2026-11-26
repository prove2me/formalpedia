-- Prove2me | solution 1 for ReweightedNPMLE.euclidean_norm_le_sqrt_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:10:05.734805+00:00
-- url     : https://prove2.me/submissions/f0579614-6421-492e-a860-b64e2b60f5b5

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

/-!
# Finite-dimensional relative-width transfer

These lemmas formalize the linear-algebra end of Proposition 4.1: a uniform
coordinatewise Taylor approximation by vectors in a low-dimensional subspace
implies the stated Euclidean residual-width bound for its orthogonal
projection.
-/

open scoped BigOperators ComplexConjugate

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Coordinatewise error `ε` gives Euclidean error at most `√n ε`. -/
theorem solution {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    {eps : ℝ} (heps : 0 ≤ eps) (hx : ∀ i, |x i| ≤ eps) :
    ‖x‖ ≤ Real.sqrt n * eps := by
  have hsum : ∑ i, (x i) ^ 2 ≤ (n : ℝ) * eps ^ 2 := by
    calc
      ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin n, eps ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        nlinarith [sq_nonneg (eps - |x i|), sq_abs (x i), hx i, abs_nonneg (x i)]
      _ = (n : ℝ) * eps ^ 2 := by simp
  rw [EuclideanSpace.norm_eq]
  calc
    Real.sqrt (∑ i, ‖x i‖ ^ 2) = Real.sqrt (∑ i, (x i) ^ 2) := by
      simp only [Real.norm_eq_abs, sq_abs]
    _ ≤ Real.sqrt ((n : ℝ) * eps ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt n * eps := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq heps]
