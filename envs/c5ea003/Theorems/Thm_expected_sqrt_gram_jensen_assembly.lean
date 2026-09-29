-- Prove2me | Theorems.Thm_expected_sqrt_gram_jensen_assembly
-- name    : expected_sqrt_gram_jensen_assembly
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:46:40.578441+00:00
-- url     : https://prove2.me/theorems/355454ff-0541-41f1-abd4-3bd9342d26c6
-- statement:
--   Outer square-root rescaling identity folding a Bernoulli expectation of the form 2*C0*sqrt(log N)*R*E[p^{-1}*sqrt(g)] into the target shape (2*C0)*(sqrt(log N / p)*R)*E[sqrt(p^{-1}*g)], using sqrt(log N / p)=sqrt(log N)*sqrt(p^{-1}) and sqrt(p^{-1}*g)=sqrt(p^{-1})*sqrt(g) (with the p=0 junk case collapsing both sides to 0). Reusable bookkeeping for expected-square-root assemblies.
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

theorem expected_sqrt_gram_jensen_assembly
    (n₁ n₂ m : ℕ) (C₀ R : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (g : Finset (Fin n₁ × Fin n₂) → ℝ) (hg : ∀ Ω, 0 ≤ g Ω) :
    2 * C₀ * Real.sqrt (Real.log (↑(max n₁ n₂))) * R *
        bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
          (fun Omega => ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ * Real.sqrt (g Omega))
      = (2 * C₀) *
          (Real.sqrt (Real.log (↑(max n₁ n₂)) / ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * R) *
          bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
            (fun Omega => Real.sqrt (((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ * g Omega)) := by sorry
