-- Prove2me | solution 1 for Martingale.norm_exp_sum_div_prod_sub_gaussian_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:25:59.62057+00:00
-- url     : https://prove2.me/submissions/904fe502-fa03-4893-bbaa-2122702b21d0

import Theorems.Thm_Martingale_exp_sum_div_prod_eq_prod
import Theorems.Thm_Martingale_norm_exp_div_one_add_I_mul_le_one
import Theorems.Thm_Martingale_norm_prod_sub_prod_le_sum
import Theorems.Thm_Martingale_norm_exp_div_one_add_sub_gaussian_le

set_option maxHeartbeats 1000000

open Finset

theorem solution {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω)
    (hsmall : ∀ k ∈ Finset.range n, |θ * Z k ω| ≤ 1) :
    ‖Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ))
          / ∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))
        - ((Real.exp (-(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2) : ℝ) : ℂ)‖
      ≤ ∑ k ∈ Finset.range n, |θ * Z k ω| ^ 3 := by
  set a : ℕ → ℂ := fun k => Complex.exp (Complex.I * θ * (Z k ω : ℂ))
    / (1 + Complex.I * θ * (Z k ω : ℂ)) with ha_def
  set b : ℕ → ℂ := fun k => ((Real.exp (-((θ * Z k ω) ^ 2) / 2) : ℝ) : ℂ) with hb_def
  -- rewrite the quotient as a product
  rw [Martingale.exp_sum_div_prod_eq_prod Z θ n ω]
  -- rewrite the Gaussian factor as a product
  have hgauss : ((Real.exp (-(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2) : ℝ) : ℂ)
      = ∏ k ∈ Finset.range n, b k := by
    have hexp : ∑ k ∈ Finset.range n, (-((θ * Z k ω) ^ 2) / 2)
        = -(θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) / 2 := by
      have hterm : ∀ k ∈ Finset.range n,
          -((θ * Z k ω) ^ 2) / 2 = (-(θ ^ 2) / 2) * Z k ω ^ 2 := fun k _ => by ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      ring
    rw [hb_def, ← Complex.ofReal_prod]
    congr 1
    rw [← hexp, Real.exp_sum]
  rw [hgauss]
  -- both families are bounded by 1 in modulus
  have hA : ∀ k, ‖a k‖ ≤ 1 := fun k => Martingale.norm_exp_div_one_add_I_mul_le_one θ (Z k ω)
  have hB : ∀ k, ‖b k‖ ≤ 1 := by
    intro k
    rw [hb_def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (θ * Z k ω)])
  refine le_trans (Martingale.norm_prod_sub_prod_le_sum a b hA hB n) ?_
  refine Finset.sum_le_sum (fun k hk => ?_)
  -- per-term cubic estimate
  have hcast : Complex.I * (θ : ℂ) * (Z k ω : ℂ) = Complex.I * ((θ * Z k ω : ℝ) : ℂ) := by
    push_cast; ring
  have h := Martingale.norm_exp_div_one_add_sub_gaussian_le (θ * Z k ω) (hsmall k hk)
  rw [ha_def, hb_def]
  simpa [hcast] using h
