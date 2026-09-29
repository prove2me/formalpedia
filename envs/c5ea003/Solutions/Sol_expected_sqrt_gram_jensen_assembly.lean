-- Prove2me | solution 1 for expected_sqrt_gram_jensen_assembly
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-25T07:46:59.450455+00:00
-- url     : https://prove2.me/submissions/5c6c28f3-9f04-44a8-aafd-862533a0c268

import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_bernoulli
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

/-!
CARVE 3 (PROVED inline) — outer `√`-rescaling fold of the Bernoulli expectation.

Pure constant/`√`-bookkeeping that turns the symmetrized+Khintchine intermediate
`2·C₀·√(log N)·R·E_Ω[p⁻¹·√(g Ω)]`
into the target shape
`(2·C₀)·√(log N / p)·R·E_Ω[√(p⁻¹·g Ω)]`,
using `√(log N / p) = √(log N)·√(p⁻¹)` and `√(p⁻¹·g) = √(p⁻¹)·√g`, so the two
`√(p⁻¹)` factors recombine with the leading `p⁻¹` (and the `p = 0` junk case
collapses both sides to `0`). Stated generically over any nonnegative statistic
`g`, hence reusable for every "expected √(operator norm)" assembly in this model.

`p := m/(n₁ n₂) ≥ 0`, `N := max n₁ n₂ ≥ 1` so `log N ≥ 0`.
-/
theorem solution
    (n₁ n₂ m : ℕ) (C₀ R : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (g : Finset (Fin n₁ × Fin n₂) → ℝ) (hg : ∀ Ω, 0 ≤ g Ω) :
    2 * C₀ * Real.sqrt (Real.log (↑(max n₁ n₂))) * R *
        bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
          (fun Omega => ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ * Real.sqrt (g Omega))
      = (2 * C₀) *
          (Real.sqrt (Real.log (↑(max n₁ n₂)) / ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) * R) *
          bernoulliExpectation ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))
            (fun Omega => Real.sqrt (((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))⁻¹ * g Omega)) := by
  set p : ℝ := (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)) with hp
  have hpos : (0:ℝ) < (n₁:ℝ)*(n₂:ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hN1 : (1:ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by
    have : 1 ≤ max n₁ n₂ := le_max_of_le_left hn₁
    exact_mod_cast this
  have hlog0 : 0 ≤ Real.log (↑(max n₁ n₂)) := Real.log_nonneg hN1
  have hL : bernoulliExpectation p (fun Omega => p⁻¹ * Real.sqrt (g Omega))
      = p⁻¹ * bernoulliExpectation p (fun Omega => Real.sqrt (g Omega)) := by
    unfold bernoulliExpectation; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω _; ring
  have hsqrtp : Real.sqrt (Real.log (↑(max n₁ n₂)) / p)
      = Real.sqrt (Real.log (↑(max n₁ n₂))) * Real.sqrt p⁻¹ := by
    rw [div_eq_mul_inv, Real.sqrt_mul hlog0]
  have hR2 : bernoulliExpectation p (fun Omega => Real.sqrt (p⁻¹ * g Omega))
      = Real.sqrt p⁻¹ * bernoulliExpectation p (fun Omega => Real.sqrt (g Omega)) := by
    unfold bernoulliExpectation; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro Ω _
    simp only
    rw [Real.sqrt_mul (by positivity)]; ring
  rw [hL, hR2, hsqrtp]
  have hpp : Real.sqrt p⁻¹ * Real.sqrt p⁻¹ = p⁻¹ := by
    rw [← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)]
  set E := bernoulliExpectation p (fun Omega => Real.sqrt (g Omega))
  set s := Real.sqrt p⁻¹
  set L := Real.sqrt (Real.log (↑(max n₁ n₂)))
  rw [show p⁻¹ = s * s from hpp.symm]
  ring
