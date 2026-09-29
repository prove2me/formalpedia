-- Prove2me | solution 1 for RainbowAP.two_mul_pow_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:22:14.042415+00:00
-- url     : https://prove2.me/submissions/620a3ab6-81ee-4a2d-b83c-454c116d27ec

-- Sol generated from Shared/RainbowAPSpectrumAsymptotics.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumThreshold

/-!
# Asymptotics of the full-spectrum threshold

We turn the two arithmetic criteria of `Shared.RainbowAPSpectrumThreshold` into real analytic
bounds, showing that for an alphabet with `N ≥ 2` letters

  `(N - 1) * log (N + 1) ≤ spectrumThreshold α ≤ N * log (2 N) + 1`.

Both sides are `N log N (1 + o(1))`, so the threshold is asymptotically `N log N`.
-/

open Finset Real

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]







open RainbowAP in
lemma solution{N m : ℕ} (hN : 2 ≤ N)
    (h : (N : ℝ) * Real.log (2 * (N : ℝ)) < m) :
    2 * N * (N - 1) ^ m < N ^ m := by
  have hNge : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hstep : ((N : ℝ) - 1) / (N : ℝ) ≤ Real.exp (-(1 / (N : ℝ))) := by
    have hexp := Real.add_one_le_exp (-(1 / (N : ℝ)))
    have heq : -(1 / (N : ℝ)) + 1 = ((N : ℝ) - 1) / (N : ℝ) := by
      field_simp
      ring
    linarith [hexp, heq.le, heq.ge]
  have hnonneg : (0 : ℝ) ≤ ((N : ℝ) - 1) / (N : ℝ) := by
    apply div_nonneg <;> linarith
  have hpow : (((N : ℝ) - 1) / (N : ℝ)) ^ m ≤ Real.exp (-((m : ℝ) / (N : ℝ))) := by
    calc (((N : ℝ) - 1) / (N : ℝ)) ^ m ≤ (Real.exp (-(1 / (N : ℝ)))) ^ m :=
          pow_le_pow_left₀ hnonneg hstep m
      _ = Real.exp (-((m : ℝ) / (N : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp
  have hEq : Real.exp (-(Real.log (2 * (N : ℝ)))) = 1 / (2 * (N : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log (by linarith), one_div]
  have hlt : Real.exp (-((m : ℝ) / (N : ℝ))) < 1 / (2 * (N : ℝ)) := by
    have hlog : Real.log (2 * (N : ℝ)) < (m : ℝ) / (N : ℝ) := by
      rw [lt_div_iff₀ hNpos]
      linarith [h]
    have h2 : Real.exp (-((m : ℝ) / (N : ℝ))) < Real.exp (-(Real.log (2 * (N : ℝ)))) :=
      Real.exp_lt_exp.2 (by linarith)
    linarith [hEq.le, hEq.ge, h2]
  have hfinal : 2 * (N : ℝ) * ((N : ℝ) - 1) ^ m < (N : ℝ) ^ m := by
    have hdiv : (((N : ℝ) - 1) / (N : ℝ)) ^ m = ((N : ℝ) - 1) ^ m / (N : ℝ) ^ m := by
      rw [div_pow]
    have hNm : (0 : ℝ) < (N : ℝ) ^ m := by positivity
    have hfr : ((N : ℝ) - 1) ^ m / (N : ℝ) ^ m < 1 / (2 * (N : ℝ)) := by
      rw [← hdiv]
      exact lt_of_le_of_lt hpow hlt
    rw [div_lt_div_iff₀ hNm (by linarith)] at hfr
    nlinarith [hfr]
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ N := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hfin : (((2 * N * (N - 1) ^ m : ℕ)) : ℝ) < ((N ^ m : ℕ) : ℝ) := by
    push_cast [hcast]
    linarith [hfinal]
  exact_mod_cast hfin
