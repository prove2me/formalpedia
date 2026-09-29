-- Prove2me | solution 1 for BanditAlgorithm.mdp_lower_bound_step_two_truncated
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-04T04:13:19.573343+00:00
-- url     : https://prove2.me/submissions/f02ccb41-5262-4cec-b80f-622392d72482

import Theorems.Thm_BanditAlgorithm_change_of_measure_deficit_pigeonhole_two_totals
import Mathlib.Data.Real.Sqrt

open Finset

theorem solution
    {ι : Type*} [Fintype ι] {k : ℕ} (hk : 2 ≤ k) (hcard : Fintype.card ι = k)
    (n D cap c₁ c₂ c₃ Δ T0 T0full slack : ℝ)
    (V Vt W R : ι → ℝ)
    (hn : 0 < n) (hD : 0 < D) (hcap0 : 0 ≤ cap) (hcap : cap ≤ n / D)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hV : ∀ j, 0 ≤ V j) (hsumV : ∑ j, V j = T0full) (hsumVt : ∑ j, Vt j = T0)
    (hT0lo : c₁ * n / D ≤ T0) (hfullhi : T0full ≤ c₂ * n / D)
    (hΔ : Δ = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (D / (2 * c₂ * n * k)))
    (hW : ∀ j, T0 - Vt j - cap * Δ * Real.sqrt (2 * V j) ≤ W j)
    (hR : ∀ j, c₃ * Δ * D * W j - slack ≤ R j) :
    ∃ j : ι,
      c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * k * n / (2 * c₂)) - slack ≤ R j := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hkR0 : (0 : ℝ) < (k : ℝ) := by positivity
  have hsq0 : 0 ≤ Real.sqrt (D / (2 * c₂ * n * k)) := Real.sqrt_nonneg _
  have hΔ0 : 0 ≤ Δ := by
    rw [hΔ]
    have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
    positivity
  have hB0 : 0 ≤ cap * Δ := by positivity
  -- Pigeonhole over the `k` alternatives, deficit and penalty on separate counts.
  obtain ⟨j, hj⟩ :=
    BanditAlgorithm.change_of_measure_deficit_pigeonhole_two_totals hk0 hcard V Vt W
      T0 T0full (cap * Δ) hV hsumV hsumVt hB0 hW
  refine ⟨j, ?_⟩
  have hT0full0 : 0 ≤ T0full := hsumV ▸ Finset.sum_nonneg fun j _ ↦ hV j
  -- The Cauchy–Schwarz penalty is at most half of the leading term.
  have hpen : Real.sqrt (2 * (k : ℝ) * T0full) ≤ Real.sqrt (2 * c₂ * n * k / D) := by
    refine Real.sqrt_le_sqrt ?_
    have hmul : T0full * (2 * (k : ℝ)) ≤ c₂ * n / D * (2 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_right hfullhi (by positivity)
    calc 2 * (k : ℝ) * T0full = T0full * (2 * (k : ℝ)) := by ring
      _ ≤ c₂ * n / D * (2 * (k : ℝ)) := hmul
      _ = 2 * c₂ * n * k / D := by field_simp
  have hsqprod :
      Real.sqrt (D / (2 * c₂ * n * k)) * Real.sqrt (2 * c₂ * n * k / D) = 1 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show D / (2 * c₂ * n * (k : ℝ)) * (2 * c₂ * n * (k : ℝ) / D) = 1 by
      field_simp]
    exact Real.sqrt_one
  have hpen2 : cap * Δ * Real.sqrt (2 * (k : ℝ) * T0full)
      ≤ n / D * (c₁ * ((k : ℝ) - 1) / 2) := by
    calc cap * Δ * Real.sqrt (2 * (k : ℝ) * T0full)
        ≤ cap * Δ * Real.sqrt (2 * c₂ * n * k / D) :=
          mul_le_mul_of_nonneg_left hpen hB0
      _ ≤ n / D * Δ * Real.sqrt (2 * c₂ * n * k / D) := by
          have : cap * Δ ≤ n / D * Δ := mul_le_mul_of_nonneg_right hcap hΔ0
          exact mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ = n / D * (c₁ * ((k : ℝ) - 1) / 2) *
            (Real.sqrt (D / (2 * c₂ * n * k)) * Real.sqrt (2 * c₂ * n * k / D)) := by
          rw [hΔ]; ring
      _ = n / D * (c₁ * ((k : ℝ) - 1) / 2) := by rw [hsqprod, mul_one]
  -- Hence `W j ≥ c₁ n (k-1) / (2 D k)`.
  have hWj : c₁ * n * ((k : ℝ) - 1) / (2 * D * k) ≤ W j := by
    refine le_trans ?_ hj
    rw [le_div_iff₀ hkR0]
    have hlead : ((k : ℝ) - 1) * (c₁ * n / D) ≤ ((k : ℝ) - 1) * T0 :=
      mul_le_mul_of_nonneg_left hT0lo (by linarith)
    have hsplit : c₁ * n * ((k : ℝ) - 1) / (2 * D) =
        ((k : ℝ) - 1) * (c₁ * n / D) - n / D * (c₁ * ((k : ℝ) - 1) / 2) := by
      field_simp; ring
    rw [show c₁ * n * ((k : ℝ) - 1) / (2 * D * (k : ℝ)) * (k : ℝ)
        = c₁ * n * ((k : ℝ) - 1) / (2 * D) by field_simp, hsplit]
    linarith [hpen2, hlead]
  -- Plug into Claim 38.11 and simplify the constant.
  have hcoef : 0 ≤ c₃ * Δ * D := by positivity
  have hchain : c₃ * Δ * D * (c₁ * n * ((k : ℝ) - 1) / (2 * D * k)) - slack ≤ R j :=
    le_trans (by linarith [mul_le_mul_of_nonneg_left hWj hcoef]) (hR j)
  refine le_trans ?_ hchain
  refine sub_le_sub_right ?_ slack
  have hsq2 : Real.sqrt (D / (2 * c₂ * n * k)) * (n * (k : ℝ))
      = Real.sqrt (D * k * n / (2 * c₂)) := by
    have hnk : (0 : ℝ) ≤ n * (k : ℝ) := by positivity
    rw [show n * (k : ℝ) = Real.sqrt ((n * (k : ℝ)) ^ 2) by rw [Real.sqrt_sq hnk],
      ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hkey : c₃ * Δ * D * (c₁ * n * ((k : ℝ) - 1) / (2 * D * k))
      = c₁ ^ 2 * c₃ * (((k : ℝ) - 1) ^ 2 / (4 * (k : ℝ) ^ 2)) *
        Real.sqrt (D * k * n / (2 * c₂)) := by
    rw [hΔ, ← hsq2]
    field_simp
    ring
  rw [hkey]
  have hratio : (1 : ℝ) / 16 ≤ ((k : ℝ) - 1) ^ 2 / (4 * (k : ℝ) ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hkR]
  have hpos : 0 ≤ Real.sqrt (D * k * n / (2 * c₂)) := Real.sqrt_nonneg _
  have hrw : c₁ ^ 2 * c₃ / 16 = c₁ ^ 2 * c₃ * (1 / 16) := by ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hratio (by positivity)) hpos
