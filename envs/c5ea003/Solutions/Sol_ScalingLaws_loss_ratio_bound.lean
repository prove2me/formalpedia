-- Prove2me | solution 1 for ScalingLaws.loss_ratio_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T23:26:34.842001+00:00
-- url     : https://prove2.me/submissions/1bbec9dc-b91f-4256-ab44-40611bb1a1b5

-- Sol generated from MachineLearning/DeterministicScalingLawEngine/ScalingLaws.lean
import Mathlib
import Definitions.Def_MachineLearning_DeterministicScalingLawEngine_ScalingLaws

/-!
# Deterministic scaling-law engine from two-sided polynomial tail bounds

This file develops a minimal, fully-compiling deterministic scaling-law engine
built from two-sided polynomial tail bounds on a loss function `L : ℕ → ℝ`.

A `TailBounds` packages a loss function together with constants `c < C` and a
decay exponent `α > 0` such that, for all `n ≥ 1`,
`c * n ^ (-α) ≤ L n ≤ C * n ^ (-α)`.

From these bounds we derive five elementary consequences relating capacity
(the index `n`, e.g. number of samples / parameters) to the achievable loss `ε`.
-/

open ScalingLaws


variable (tb : TailBounds)







open ScalingLaws in
theorem solution:
    ∀ n m : ℕ, 1 ≤ n → 1 ≤ m → m ≤ n →
      tb.L n / tb.L m ≤ (tb.C / tb.c) * ((m : ℝ) / n) ^ tb.α := by
  intros n m hn hm hmn
  have h_bound : tb.L n / tb.L m ≤ (tb.C * (n : ℝ) ^ (-tb.α)) / (tb.c * (m : ℝ) ^ (-tb.α)) := by
    gcongr
    · exact mul_nonneg (le_of_lt (by linarith [tb.c_pos, tb.c_lt_C])) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · exact mul_pos tb.c_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hm) _)
    · exact tb.upper n hn
    · exact tb.lower m hm
  refine h_bound.trans_eq ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hm0 : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  rw [Real.div_rpow hm0.le hn0.le, Real.rpow_neg hn0.le, Real.rpow_neg hm0.le]
  field_simp
