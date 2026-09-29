-- Prove2me | solution 1 for Martingale.norm_prod_one_add_I_mul_sq
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T18:51:29.522263+00:00
-- url     : https://prove2.me/submissions/ee1a6184-f711-468c-beb9-e9582b482bf5

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset

theorem solution {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    ‖∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))‖ ^ 2
      = ∏ k ∈ Finset.range n, (1 + θ ^ 2 * Z k ω ^ 2) := by
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring
