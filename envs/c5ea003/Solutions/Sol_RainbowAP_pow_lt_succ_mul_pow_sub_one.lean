-- Prove2me | solution 1 for RainbowAP.pow_lt_succ_mul_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:22:12.222694+00:00
-- url     : https://prove2.me/submissions/a4794e77-70c6-4b5b-b094-8f2c7240fb2a

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
    (h : (m : ℝ) < ((N : ℝ) - 1) * Real.log ((N : ℝ) + 1)) :
    N ^ m < (N + 1) * (N - 1) ^ m := by
  have hNge : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hxpos : (0 : ℝ) < (N : ℝ) / ((N : ℝ) - 1) := by positivity
  have hxm1 : (N : ℝ) / ((N : ℝ) - 1) - 1 = 1 / ((N : ℝ) - 1) := by
    field_simp
    ring
  have hlogx : Real.log ((N : ℝ) / ((N : ℝ) - 1)) ≤ 1 / ((N : ℝ) - 1) := by
    have hle := Real.log_le_sub_one_of_pos hxpos
    linarith [hxm1]
  have hmlog : (m : ℝ) * Real.log ((N : ℝ) / ((N : ℝ) - 1)) < Real.log ((N : ℝ) + 1) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have h1 : (m : ℝ) * Real.log ((N : ℝ) / ((N : ℝ) - 1)) ≤ (m : ℝ) * (1 / ((N : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left hlogx hm0
    have h2 : (m : ℝ) * (1 / ((N : ℝ) - 1)) < Real.log ((N : ℝ) + 1) := by
      rw [mul_one_div, div_lt_iff₀ hNpos]
      linarith [h]
    linarith
  have hxm : ((N : ℝ) / ((N : ℝ) - 1)) ^ m < (N : ℝ) + 1 := by
    have h1 : ((N : ℝ) / ((N : ℝ) - 1)) ^ m
        = Real.exp ((m : ℝ) * Real.log ((N : ℝ) / ((N : ℝ) - 1))) := by
      rw [Real.exp_nat_mul, Real.exp_log hxpos]
    have h2 : Real.exp ((m : ℝ) * Real.log ((N : ℝ) / ((N : ℝ) - 1)))
        < Real.exp (Real.log ((N : ℝ) + 1)) := Real.exp_lt_exp.2 hmlog
    rw [Real.exp_log (by linarith)] at h2
    rw [h1]
    exact h2
  have hden : (0 : ℝ) < ((N : ℝ) - 1) ^ m := by positivity
  have hkey : (N : ℝ) ^ m < ((N : ℝ) + 1) * ((N : ℝ) - 1) ^ m := by
    have hdiv : ((N : ℝ) / ((N : ℝ) - 1)) ^ m = (N : ℝ) ^ m / ((N : ℝ) - 1) ^ m := by
      rw [div_pow]
    rw [hdiv, div_lt_iff₀ hden] at hxm
    linarith [hxm]
  have hcast : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    have h1 : (1 : ℕ) ≤ N := by omega
    push_cast [Nat.cast_sub h1]
    ring
  have hfin : ((N ^ m : ℕ) : ℝ) < (((N + 1) * (N - 1) ^ m : ℕ) : ℝ) := by
    push_cast [hcast]
    exact hkey
  exact_mod_cast hfin
