-- Prove2me | solution 2 for quadratic_neumann_middle_index_distinct_mean_coefficients_from_kernel_square_base_bounds_min_dim_shifted
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T19:15:39.4655+00:00
-- url     : https://prove2.me/submissions/3e6153a2-3503-48c3-92a4-a9cc6e1bd87b

import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
import Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails
import Mathlib.Tactic

open MatrixCompletion
open scoped Classical BigOperators

private theorem bernoulliEventProb_mono_of_nonneg_weight
    {n₁ n₂ : ℕ} {p : ℝ}
    {Event Event' : Finset (Fin n₁ × Fin n₂) → Prop}
    (hweight : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      0 ≤ bernoulliObservationWeight p Omega)
    (hmono : ∀ Omega, Event Omega → Event' Omega) :
    bernoulliEventProb p Event ≤ bernoulliEventProb p Event' := by
  unfold bernoulliEventProb
  refine Finset.sum_le_sum ?_
  intro Omega hOmega
  by_cases hEvent : Event Omega
  · simp [hEvent, hmono Omega hEvent]
  · by_cases hEvent' : Event' Omega
    · simp [hEvent, hEvent', hweight Omega]
    · simp [hEvent, hEvent']

private theorem bernoulliObservationWeight_nonneg_of_nonneg_rate
    {n₁ n₂ : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) :
    0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

private theorem sample_ratio_nonneg
    {n₁ n₂ m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
  have hden_pos : 0 < ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  exact div_nonneg (by positivity) (le_of_lt hden_pos)

private theorem sample_ratio_le_one
    {n₁ n₂ m : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (hm : m ≤ n₁ * n₂) :
    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  have hden_pos : 0 < ((n₁ : ℝ) * (n₂ : ℝ)) := by positivity
  have hm' : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
    exact_mod_cast hm
  exact (div_le_one hden_pos).mpr hm'

private theorem sqrt_beta_shift_le_sqrt_two_mul
    (β L : ℝ) (hβ : 2 < β) (hL : 0 ≤ L) :
    Real.sqrt ((β + 2) * L) ≤ Real.sqrt (2 : ℝ) * Real.sqrt (β * L) := by
  have hβ_nonneg : 0 ≤ β := by linarith
  have hβL_nonneg : 0 ≤ β * L := mul_nonneg hβ_nonneg hL
  have harg : (β + 2) * L ≤ 2 * (β * L) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hβ)) hL]
  calc
    Real.sqrt ((β + 2) * L) ≤ Real.sqrt (2 * (β * L)) :=
      Real.sqrt_le_sqrt harg
    _ = Real.sqrt (2 : ℝ) * Real.sqrt (β * L) := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]

theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
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
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              ((β + 2) * Real.log (↑(max n₁ n₂))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          ∀ Omega : Finset (Fin n₁ × Fin n₂),
          quadraticMiddleIndexDistinctMeanCoefficient Omega S
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1 =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Centry * μ₀ ^ 2 *
              (((r : ℝ) / (↑(min n₁ n₂))) ^ 2)) →
        (∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                    Real.rpow
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                      ((3 : ℝ) / 2))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfrob
  rcases
      quadratic_neumann_middle_index_distinct_mean_coefficient_pointwise_tail_from_kernel_square_base_bounds_min_dim
        Centry Cfro hCentry hCfrob with
    ⟨Cpoint, cpoint, hCpoint, hcpoint, hpoint⟩
  have hsqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hCpoint' : 0 < Cpoint * Real.sqrt (2 : ℝ) :=
    mul_pos hCpoint hsqrt_two_pos
  rcases
      quadratic_neumann_middle_index_distinct_mean_coefficients_uniform_from_shifted_pointwise_tails
        (Cpoint * Real.sqrt (2 : ℝ)) cpoint hCpoint' hcpoint with
    ⟨Ccoef, ccoef, hCcoef, hccoef, huniform⟩
  refine ⟨Ccoef, ccoef, hCcoef, hccoef, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
    hsampleβ hsampleβ2 hrepr hentry hfrob
  refine
    huniform β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
      hsampleβ ?_
  intro w1
  have hsmall :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
              Cpoint *
                Real.sqrt ((β + 2) * Real.log (↑(max n₁ n₂))) *
                  Real.rpow
                    ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                    ((3 : ℝ) / 2)) ≥
        1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) :=
    hpoint (β + 2) lam (by linarith) hlam n₁ n₂ r m M μ₀ μ₁ S
      hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1 hsampleβ2 w1
      (hrepr w1) (hentry w1) (hfrob w1)
  have hp0 : 0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
    sample_ratio_nonneg hn₁ hn₂
  have hp1 : ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 :=
    sample_ratio_le_one hn₁ hn₂ hm
  have hweight :
      ∀ Omega : Finset (Fin n₁ × Fin n₂),
        0 ≤ bernoulliObservationWeight
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) Omega :=
    bernoulliObservationWeight_nonneg_of_nonneg_rate hp0 hp1
  have hN_pos : 0 < max n₁ n₂ :=
    lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_one : (1 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by
    exact_mod_cast hN_pos
  have hlog_nonneg : 0 ≤ Real.log (↑(max n₁ n₂) : ℝ) :=
    Real.log_nonneg hN_one
  have hbase_nonneg :
      0 ≤ ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) := by
    refine div_nonneg ?_ (by positivity)
    exact mul_nonneg (mul_nonneg (le_trans zero_le_one hμ₀) (by positivity)) (by positivity)
  have hscale_nonneg :
      0 ≤
        Real.rpow
          ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
          ((3 : ℝ) / 2) :=
    Real.rpow_nonneg hbase_nonneg _
  have hsqrt_le :
      Real.sqrt ((β + 2) * Real.log (↑(max n₁ n₂))) ≤
        Real.sqrt (2 : ℝ) * Real.sqrt (β * Real.log (↑(max n₁ n₂))) :=
    sqrt_beta_shift_le_sqrt_two_mul β (Real.log (↑(max n₁ n₂))) hβ hlog_nonneg
  have hmono :
      bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
              Cpoint *
                Real.sqrt ((β + 2) * Real.log (↑(max n₁ n₂))) *
                  Real.rpow
                    ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                    ((3 : ℝ) / 2)) ≤
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
          (fun Omega =>
            |quadraticMiddleIndexDistinctMeanCoefficient Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
              (Cpoint * Real.sqrt (2 : ℝ)) *
                Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
                  Real.rpow
                    ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                    ((3 : ℝ) / 2)) := by
    refine bernoulliEventProb_mono_of_nonneg_weight hweight ?_
    intro Omega hOmega
    refine le_trans hOmega ?_
    calc
      Cpoint * Real.sqrt ((β + 2) * Real.log (↑(max n₁ n₂))) *
          Real.rpow
            ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
            ((3 : ℝ) / 2)
          ≤ Cpoint *
              (Real.sqrt (2 : ℝ) *
                Real.sqrt (β * Real.log (↑(max n₁ n₂)))) *
              Real.rpow
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                ((3 : ℝ) / 2) := by
            exact
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hsqrt_le (le_of_lt hCpoint))
                hscale_nonneg
      _ = (Cpoint * Real.sqrt (2 : ℝ)) *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
              Real.rpow
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                ((3 : ℝ) / 2) := by ring
  linarith
