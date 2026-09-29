-- Prove2me | solution 1 for Martingale.exp_sum_div_prod_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T18:58:44.575029+00:00
-- url     : https://prove2.me/submissions/771211b9-7d41-41df-b0e4-c24961da6d3e

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exponential

open Finset

theorem solution {Ω : Type*} (Z : ℕ → Ω → ℝ) (θ : ℝ) (n : ℕ) (ω : Ω) :
    Complex.exp (Complex.I * θ * ((∑ k ∈ Finset.range n, Z k ω : ℝ) : ℂ))
        / ∏ k ∈ Finset.range n, (1 + Complex.I * θ * (Z k ω : ℂ))
      = ∏ k ∈ Finset.range n, (Complex.exp (Complex.I * θ * (Z k ω : ℂ))
          / (1 + Complex.I * θ * (Z k ω : ℂ))) := by
  rw [Finset.prod_div_distrib]
  congr 1
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]
