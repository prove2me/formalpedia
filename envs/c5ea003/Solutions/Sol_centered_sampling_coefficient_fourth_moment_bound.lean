-- Prove2me | solution 1 for centered_sampling_coefficient_fourth_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T23:13:45.273093+00:00
-- url     : https://prove2.me/submissions/0b91e72f-06bf-47f2-9ae8-acc6dccfc48e

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_centered_sampling_coefficient_fourth_moment
import Theorems.Thm_centered_sampling_coefficient_second_moment
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 3200000

/-- Reusable cross-term bound: dropping the diagonal from a doubly-indexed product
sum and completing it gives the square of the single sum. -/
private theorem cross_le_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ a, ∑ b, (if a = b then (0:ℝ) else f a * f b)) ≤ (∑ a, f a) ^ 2 := by
  have hexp : (∑ a, f a) ^ 2 = ∑ a, ∑ b, f a * f b := by
    rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  apply Finset.sum_le_sum; intro a _
  apply Finset.sum_le_sum; intro b _
  by_cases h : a = b
  · simp only [h, if_true]; exact mul_nonneg (hf _) (hf _)
  · simp only [h, if_false]; exact le_refl _

/-- **Bernstein fourth-moment bound** for the scalar centered sampling coefficient.
For $0<p\le 1$,
$$\mathbb E[\mathrm{Coeff}^4]\le 3\,(\mathbb E[\mathrm{Coeff}^2])^2+\sum_w p^{-3}(1-p)B_w^4.$$ -/
theorem solution {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    bernoulliExpectation p
      (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 4) ≤
      3 * (bernoulliExpectation p
            (fun Omega => (matrixEntrySum (centeredSamplingFluctuation Omega p B)) ^ 2)) ^ 2
      + ∑ w : Fin n₁ × Fin n₂, p⁻¹^3 * (1 - p) * (B w.1 w.2)^4 := by
  classical
  have hp : p ≠ 0 := ne_of_gt hp0
  rw [centered_sampling_coefficient_fourth_moment p hp B,
      centered_sampling_coefficient_second_moment p hp B]
  -- σ² = ((1-p)/p) * frobeniusNormSq B = ∑_w μ₂(w)
  have hsig : ((1 - p) / p) * frobeniusNormSq B
      = ∑ w : Fin n₁ × Fin n₂, ((1 - p) / p) * (B w.1 w.2)^2 := by
    rw [← Finset.mul_sum]
    congr 1
    rw [Fintype.sum_prod_type]
    rfl
  -- cross bound: 3·∑_{a≠b} μ₂μ₂ ≤ 3·σ²²
  have hcross : 3 * (∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
      (if a = b then (0:ℝ) else
        (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2)))
      ≤ 3 * (((1 - p) / p) * frobeniusNormSq B) ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [hsig]
    have hmu2 : (0:ℝ) ≤ (1 - p) / p := div_nonneg (by linarith) hp0.le
    exact cross_le_sq (fun (w : Fin n₁ × Fin n₂) => ((1 - p) / p) * (B w.1 w.2)^2)
      (fun w => mul_nonneg hmu2 (sq_nonneg _))
  -- diagonal bound: termwise then summed
  have hdiag : ∀ w : Fin n₁ × Fin n₂,
      (p * (p⁻¹ * (B w.1 w.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p))^4)
      ≤ p⁻¹^3 * (1 - p) * (B w.1 w.2)^4 := by
    intro w
    set x := B w.1 w.2 with hx
    have h1p : 0 ≤ 1 - p := by linarith
    have hpinv : 0 < p⁻¹ := by positivity
    -- LHS = p⁻¹^3 * (1-p) * x^4 * ((1-p)^3 + p^3)
    have heq : (p * (p⁻¹ * x * (1 - p))^4 + (1 - p) * (p⁻¹ * x * (0 - p))^4)
        = p⁻¹^3 * (1 - p) * x^4 * ((1 - p)^3 + p^3) := by
      field_simp
      ring
    rw [heq]
    -- (1-p)^3 + p^3 ≤ 1, and the prefactor p⁻¹^3 (1-p) x^4 ≥ 0
    have hpre : 0 ≤ p⁻¹^3 * (1 - p) * x^4 := by positivity
    have hbr : (1 - p)^3 + p^3 ≤ 1 := by nlinarith [mul_nonneg h1p hp0.le, hp1, hp0.le]
    calc p⁻¹^3 * (1 - p) * x^4 * ((1 - p)^3 + p^3)
        ≤ p⁻¹^3 * (1 - p) * x^4 * 1 := by
          apply mul_le_mul_of_nonneg_left hbr hpre
      _ = p⁻¹^3 * (1 - p) * x^4 := by ring
  have hdiagsum :
      (∑ w : Fin n₁ × Fin n₂,
        (p * (p⁻¹ * (B w.1 w.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p))^4))
      ≤ ∑ w : Fin n₁ × Fin n₂, p⁻¹^3 * (1 - p) * (B w.1 w.2)^4 :=
    Finset.sum_le_sum (fun w _ => hdiag w)
  -- generalize the giant sum atoms to prevent whnf normalization in the final linarith
  set Dsum := (∑ w : Fin n₁ × Fin n₂,
        (p * (p⁻¹ * (B w.1 w.2) * (1 - p))^4 + (1 - p) * (p⁻¹ * (B w.1 w.2) * (0 - p))^4))
    with hDsum
  set CR := (∑ a : Fin n₁ × Fin n₂, ∑ b : Fin n₁ × Fin n₂,
      (if a = b then (0:ℝ) else
        (((1 - p) / p) * (B a.1 a.2)^2) * (((1 - p) / p) * (B b.1 b.2)^2))) with hCR
  set Dbound := (∑ w : Fin n₁ × Fin n₂, p⁻¹^3 * (1 - p) * (B w.1 w.2)^4) with hDbound
  set SS := (((1 - p) / p) * frobeniusNormSq B) ^ 2 with hSS
  linarith [hdiagsum, hcross]
