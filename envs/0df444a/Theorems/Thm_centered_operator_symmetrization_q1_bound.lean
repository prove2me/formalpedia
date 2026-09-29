-- Prove2me | Theorems.Thm_centered_operator_symmetrization_q1_bound
-- name    : centered_operator_symmetrization_q1_bound
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:46:01.763466+00:00
-- url     : https://prove2.me/theorems/985105c5-e066-4520-978a-fad915c8cfa9
-- statement:
--   Bernoulli-to-Rademacher symmetrization at the operator-norm level (q=1) for the centered selected rank-one tangent Gram: the expected p-inverse-scaled operator norm of the centered sum is at most twice the same expectation with an inner uniform sign-average. Specialisation of the symmetrization contraction inequality to the L2-operator norm. (Candes-Recht 2009, Section 9.1.)
-- source:
--   Candes, Recht, Exact Matrix Completion via Convex Optimization (2009), Section 9.1

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

theorem centered_operator_symmetrization_q1_bound
    (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
    (S : SVD M r)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r) (hm : m ≤ n₁ * n₂) :
    bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
        (fun Omega => ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ *
          ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
            (∑ ab : Fin n₁ × Fin n₂,
              (((if ab ∈ Omega then (1:ℝ) else 0) - (m:ℝ)/((n₁:ℝ)*(n₂:ℝ))) •
                Matrix.vecMulVec
                  (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                  (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)
      ≤ 2 * bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
          (fun Omega => ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ *
            (∑ Es : Finset (Fin n₁ × Fin n₂),
              ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (((if ab ∈ Es then (1:ℝ) else -1) *
                        (if ab ∈ Omega then (1:ℝ) else 0)) •
                      Matrix.vecMulVec
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)) := by sorry
