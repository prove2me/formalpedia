-- Prove2me | solution 1 for Martingale.norm_prod_one_add_I_mul_bounds
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T18:55:08.896809+00:00
-- url     : https://prove2.me/submissions/52c1881f-9d51-4d4e-8672-9ee3949d3831

import Theorems.Thm_Martingale_norm_prod_one_add_I_mul_sq

open Finset

theorem solution {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    1 ≤ ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ∧
    ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ^ 2
      ≤ Real.exp (θ ^ 2 * ∑ k ∈ Finset.range n, Z k ω ^ 2) := by
  have hid := Martingale.norm_prod_one_add_I_mul_sq Z θ n ω
  have hnn : ∀ k, (0:ℝ) ≤ θ ^ 2 * Z k ω ^ 2 := fun k =>
    mul_nonneg (sq_nonneg θ) (sq_nonneg (Z k ω))
  constructor
  · have hge : (1:ℝ) ≤ ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ^ 2 := by
      rw [hid]
      calc (1:ℝ) = ∏ _k ∈ Finset.range n, (1:ℝ) := by simp
        _ ≤ ∏ k ∈ Finset.range n, (1 + θ ^ 2 * Z k ω ^ 2) :=
            Finset.prod_le_prod (fun _ _ => zero_le_one) (fun k _ => by linarith [hnn k])
    nlinarith [norm_nonneg (∏ k ∈ Finset.range n, ((1:ℂ) + Complex.I * θ * (Z k ω : ℂ)))]
  · rw [hid, Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod (fun k _ => by linarith [hnn k]) (fun k _ => ?_)
    linarith [Real.add_one_le_exp (θ ^ 2 * Z k ω ^ 2)]
