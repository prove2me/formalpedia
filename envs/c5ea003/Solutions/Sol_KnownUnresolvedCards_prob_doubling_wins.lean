-- Prove2me | solution 1 for KnownUnresolvedCards.prob_doubling_wins
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:03:40.445987+00:00
-- url     : https://prove2.me/submissions/994c07e0-1153-48ec-9a4c-ffe306fb6932

-- Sol generated from MachineLearning/KnownUnresolvedCards/BettingSystem.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_BettingSystem
import Theorems.Thm_KnownUnresolvedCards_E_def
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — VI. No betting system beats a fair book

The previous files price a *fixed* menu of cards.  This file closes the loop by
letting the gambler be maximally adaptive: after every fair coin toss she may
choose a completely arbitrary new stake — of either sign, of any size, depending
on the whole history — and she may quit at any time (encoded by staking `0`).

`expGain_eq_zero` says that the expected net gain of *any* such system over any
finite horizon is exactly `0`.  This is the finite-horizon optional stopping
theorem, proved here by a two-line induction on the horizon, and it is the
strongest form of "uncertainty supplies no positive edge": not only does a
random card have no value, no adaptive scheme built out of random cards has any
value either.

The second half of the file is the standard adversarial objection — the
**doubling (martingale) system**, which wins with probability `1 - 2^{-n}` — and
its resolution: the rare loss is exactly large enough to cancel the frequent
gain.  `doubling_paradox` states the two facts side by side.

## Main results

* `expGain_eq_zero` — no adaptive betting system has an edge at fair odds.
* `optional_stopping_no_edge` — the same with an explicit stopping rule.
* `doubling_net_after_win` — the geometric-series identity `2^k - (2^k - 1) = 1`
  that makes the doubling system's net gain equal to `1` after any win.
* `E_doublingGain` — the doubling system has zero expected gain, and
* `prob_doubling_wins` — it nevertheless wins with probability `1 - 2^{-n}`.
* `doubling_paradox` — both, together with the fact that the win probability can
  be pushed arbitrarily close to `1`.
-/


open KnownUnresolvedCards

open Finset

/-! ## Adaptive betting systems -/





/-! ## The doubling system -/









open KnownUnresolvedCards in
theorem solution(n : ℕ) :
    E (fun w : Fin n → Bool => if 0 < doublingGain n w then (1 : ℚ) else 0) = 1 - (1 / 2) ^ n := by
  classical
  have hpos : ∀ w : Fin n → Bool, (0 < doublingGain n w) ↔ w ≠ allFalse n := by
    intro w
    by_cases h : w = allFalse n
    · subst h
      simp only [doublingGain, ne_eq, not_true_eq_false, iff_false, not_lt, if_pos]
      have : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      linarith
    · simp [doublingGain, h]
  have hsum : ∑ w : Fin n → Bool, (if 0 < doublingGain n w then (1 : ℚ) else 0)
      = ((2 : ℚ) ^ n - 1) := by
    rw [Finset.sum_congr rfl (fun w _ => by rw [if_congr (hpos w) rfl rfl])]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (allFalse n))]
    rw [if_neg (by simp)]
    rw [Finset.sum_congr rfl (fun w hw => if_pos (Finset.mem_erase.mp hw).1)]
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    simp
  rw [E_def, hsum]
  have hc : (Fintype.card (Fin n → Bool) : ℚ) = 2 ^ n := by simp
  rw [hc]
  have h2 : ((2 : ℚ) ^ n) ≠ 0 := by positivity
  have h3 : ((1 : ℚ) / 2) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  field_simp
  linarith
