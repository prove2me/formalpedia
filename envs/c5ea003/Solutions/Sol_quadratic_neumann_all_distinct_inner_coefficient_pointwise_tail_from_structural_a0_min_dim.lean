-- Prove2me | solution 1 for quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_structural_a0_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-30T15:08:58.670092+00:00
-- url     : https://prove2.me/submissions/8ebaec68-10e1-4ec9-9874-4541288153d2

import Theorems.Thm_quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim
import Theorems.Thm_a0_implies_default_a1_parameter

open MatrixCompletion
open scoped Classical BigOperators

private theorem one_le_defaultA1Parameter_of_one_le_mu0
    {r : ℕ} {μ₀ : ℝ} (hμ₀ : 1 <= μ₀) (hr : 0 < r) :
    1 <= defaultA1Parameter μ₀ r := by
  have hr_real : (1 : ℝ) <= (r : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hr)
  have hsqrt : (1 : ℝ) <= Real.sqrt (r : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hr_real
  have hmul : (1 : ℝ) * 1 <= μ₀ * Real.sqrt (r : ℝ) :=
    mul_le_mul hμ₀ hsqrt (by norm_num) (le_trans (by norm_num) hμ₀)
  simpa [defaultA1Parameter] using hmul

theorem solution :
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ (Omega3 : Finset (Fin n₁ × Fin n₂))
            (w1 w2 : Fin n₁ × Fin n₂),
          quadraticAllDistinctInnerCoefficient Omega3 S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega3
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticAllDistinctInnerBaseMatrix S w1 w2))) →
        ∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega3 =>
                |quadraticAllDistinctInnerCoefficient Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 w2| ≤
                  Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_all_distinct_inner_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry, hentry⟩
  rcases quadratic_neumann_all_distinct_inner_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro, hfro⟩
  rcases quadratic_neumann_all_distinct_inner_coefficient_pointwise_tail_from_base_bounds_min_dim
      Centry Cfro hCentry hCfro with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hpoint⟩
  refine ⟨Cpoint, cpoint, hCpoint, hcpoint, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ _hμ₁ hA0 _hA1
    hsample hrepr w1 w2
  have hμ₀_nonneg : 0 <= μ₀ := le_trans (by norm_num) hμ₀
  have hA1default :
      A1 S (defaultA1Parameter μ₀ r) :=
    a0_implies_default_a1_parameter n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀_nonneg hA0
  have hdefault_ge_one : 1 <= defaultA1Parameter μ₀ r :=
    one_le_defaultA1Parameter_of_one_le_mu0 hμ₀ hr
  exact
    hpoint β lam hβ hlam n₁ n₂ r m M μ₀ (defaultA1Parameter μ₀ r) S
      hn₁ hn₂ hr hm hμ₀ hdefault_ge_one hA0 hA1default hsample hrepr
      (hentry n₁ n₂ r M μ₀ (defaultA1Parameter μ₀ r) S
        hn₁ hn₂ hr hμ₀ hdefault_ge_one hA0 hA1default)
      (hfro n₁ n₂ r M μ₀ (defaultA1Parameter μ₀ r) S
        hn₁ hn₂ hr hμ₀ hdefault_ge_one hA0 hA1default)
      w1 w2
