-- Prove2me | solution 1 for a0_implies_default_a1_parameter
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T14:50:23.642037+00:00
-- url     : https://prove2.me/submissions/e902d906-32ff-4159-acba-787cf14e7ae8

import Definitions.Def_matrix_completion_svd

open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletionA0DefaultA1

private theorem coordinate_sq_sum_le_of_coherence
    {N r : Nat} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r -> Fin N -> ℝ) (μ : ℝ)
    (hcoh : coherence N r u <= μ) (i : Fin N) :
    (∑ k : Fin r, (u k i) ^ 2) <= μ * (r : ℝ) / (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  let U : ℝ := ⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2
  have hi_le : (∑ k : Fin r, (u k i) ^ 2) <= U := by
    exact le_ciSup (Finite.bddAbove_range fun i : Fin N => ∑ k : Fin r, (u k i) ^ 2) i
  have hfactor_pos : 0 < (N : ℝ) / (r : ℝ) := div_pos hNreal hrreal
  have hmul : ((N : ℝ) / (r : ℝ)) * U <= μ := by
    simpa [coherence, U] using hcoh
  have hU_le_div : U <= μ / ((N : ℝ) / (r : ℝ)) := by
    rw [le_div_iff₀ hfactor_pos]
    simpa [mul_comm] using hmul
  have hdiv : μ / ((N : ℝ) / (r : ℝ)) = μ * (r : ℝ) / (N : ℝ) := by
    field_simp [ne_of_gt hNreal, ne_of_gt hrreal]
  exact hi_le.trans (by simpa [hdiv] using hU_le_div)

private theorem sqrt_default_product
    {n₁ n₂ r : Nat} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    {μ₀ : ℝ} (hμ₀ : 0 <= μ₀) :
    Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) =
      μ₀ * Real.sqrt (r : ℝ) *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  have hn₁real : 0 < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂real : 0 < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrreal : 0 < (r : ℝ) := by exact_mod_cast hr
  have hleft_nonneg : 0 <= μ₀ * (r : ℝ) / (n₁ : ℝ) := by positivity
  calc
    Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
        Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ))
        = Real.sqrt
            ((μ₀ * (r : ℝ) / (n₁ : ℝ)) * (μ₀ * (r : ℝ) / (n₂ : ℝ))) := by
            rw [Real.sqrt_mul hleft_nonneg]
    _ = Real.sqrt
            (μ₀ ^ 2 * ((r : ℝ) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            congr 1
            field_simp [ne_of_gt hn₁real, ne_of_gt hn₂real]
    _ = Real.sqrt (μ₀ ^ 2) *
            Real.sqrt (((r : ℝ) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            rw [Real.sqrt_mul (sq_nonneg μ₀)]
    _ = μ₀ * Real.sqrt (((r : ℝ) ^ 2 / ((n₁ : ℝ) * (n₂ : ℝ))) ) := by
            rw [Real.sqrt_sq hμ₀]
    _ = μ₀ *
          Real.sqrt ((r : ℝ) * ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            congr 1
            congr 1
            field_simp [ne_of_gt hn₁real, ne_of_gt hn₂real]
    _ = μ₀ * (Real.sqrt (r : ℝ) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
            rw [Real.sqrt_mul (le_of_lt hrreal)]
    _ = μ₀ * Real.sqrt (r : ℝ) *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
            ring

private theorem a0_to_default_a1
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (μ₀ : ℝ) (S : SVD M r) :
    0 < n₁ -> 0 < n₂ -> 0 < r ->
    0 <= μ₀ -> A0 S μ₀ -> A1 S (defaultA1Parameter μ₀ r) := by
  intro hn₁ hn₂ hr hμ₀ hA0 i j
  have hsumu_nonneg : 0 <= ∑ k : Fin r, (S.u k i) ^ 2 := by
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.u k i)
  have hsumv_nonneg : 0 <= ∑ k : Fin r, (S.v k j) ^ 2 := by
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.v k j)
  have hsumu_le :
      (∑ k : Fin r, (S.u k i) ^ 2) <= μ₀ * (r : ℝ) / (n₁ : ℝ) :=
    coordinate_sq_sum_le_of_coherence hn₁ hr S.u μ₀ hA0.1 i
  have hsumv_le :
      (∑ k : Fin r, (S.v k j) ^ 2) <= μ₀ * (r : ℝ) / (n₂ : ℝ) :=
    coordinate_sq_sum_le_of_coherence hn₂ hr S.v μ₀ hA0.2 j
  have hsumu_bound_nonneg : 0 <= μ₀ * (r : ℝ) / (n₁ : ℝ) := by
    positivity
  have hcsq :
      (∑ k : Fin r, S.u k i * S.v k j) ^ 2 <=
        (∑ k : Fin r, (S.u k i) ^ 2) * (∑ k : Fin r, (S.v k j) ^ 2) := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin r))
        (fun k : Fin r => S.u k i) (fun k : Fin r => S.v k j))
  have habs_le :
      |∑ k : Fin r, S.u k i * S.v k j| <=
        Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2)) :=
    Real.abs_le_sqrt hcsq
  have hsqrt_le :
      Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2)) <=
        Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
    have hprod_le :
        (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) <=
          (μ₀ * (r : ℝ) / (n₁ : ℝ)) * (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
      exact mul_le_mul hsumu_le hsumv_le hsumv_nonneg hsumu_bound_nonneg
    calc
      Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2))
          <= Real.sqrt ((μ₀ * (r : ℝ) / (n₁ : ℝ)) *
              (μ₀ * (r : ℝ) / (n₂ : ℝ))) := Real.sqrt_le_sqrt hprod_le
      _ = Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
            rw [Real.sqrt_mul]
            positivity
  have hsign_eq :
      signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
    rw [signMatrix]
    simpa [Matrix.vecMulVec_apply] using
      (Matrix.sum_apply i j (Finset.univ : Finset (Fin r))
        (fun k : Fin r => Matrix.vecMulVec (S.u k) (S.v k)))
  calc
    |signMatrix S i j|
        = |∑ k : Fin r, S.u k i * S.v k j| := by rw [hsign_eq]
    _ <= Real.sqrt ((∑ k : Fin r, (S.u k i) ^ 2) *
          (∑ k : Fin r, (S.v k j) ^ 2)) := habs_le
    _ <= Real.sqrt (μ₀ * (r : ℝ) / (n₁ : ℝ)) *
          Real.sqrt (μ₀ * (r : ℝ) / (n₂ : ℝ)) := hsqrt_le
    _ = defaultA1Parameter μ₀ r *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
            rw [defaultA1Parameter, sqrt_default_product hn₁ hn₂ hr hμ₀]

end MatrixCompletionA0DefaultA1

theorem solution :
    ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ -> 0 < n₂ -> 0 < r ->
      0 <= μ₀ -> A0 S μ₀ -> A1 S (defaultA1Parameter μ₀ r) := by
  intro n₁ n₂ r M μ₀ S
  exact MatrixCompletionA0DefaultA1.a0_to_default_a1 μ₀ S
