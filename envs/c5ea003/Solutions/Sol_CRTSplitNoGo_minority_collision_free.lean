-- Prove2me | solution 1 for CRTSplitNoGo.minority_collision_free
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:58:00.150819+00:00
-- url     : https://prove2.me/submissions/349891bd-c277-45b1-baf4-09b2834b7fd2

-- Sol generated from Bridges/CRTSplitNoGoBirthdayTail.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail
import Theorems.Thm_CRTSplitNoGo_card_injPrefix_le_exp

/-!
# The CRT-Split No-Go, Part VII: the birthday *window* and the exact Pollard reveal time

Part VI proved the exact birthday law `card_injPrefix` for orbit prefixes and derived its
lower half (`majority_collision_free`): at time `T` with `T (T+1) ≤ n` at least half of all
`n ^ n` maps of an `n`-element set still have a collision-free orbit prefix.  That is only one
side of a threshold.  This file closes the loop by proving the matching *upper* half — an
exponential tail — and it settles the easy half of the smoothness-regime conjecture by
computing the Pollard `p-1` reveal time exactly.

## Main results

* `card_injPrefix_le_exp` — the exact birthday product is dominated by a Gaussian tail:
  `#{f : collision-free prefix of length T+1} ≤ exp (-T(T+1)/(2n)) · n ^ n`.
  This is Conjecture 1 of the previous cycle's `FUTURE_DIRECTIONS.md`, now a theorem.
* `minority_collision_free` — consequently, once `4 n ≤ T (T+1)` (i.e. `T ≳ 2√n`) at most a
  quarter of all maps are collision-free.
* `birthday_window_zmod` — the two halves together, on the state space `ZMod p` of the reduced
  dynamics: the collision-free fraction passes from `≥ 1/2` to `≤ 1/4` inside the window
  `√p ≲ T ≲ 2√p`.  The first cycle closure — the only factor-revealing event, by Parts I–IV —
  therefore happens at `T ≍ √p = N^{1/4}`, exponentially far in `log N`.
* `pm1RevealTime_eq_min_orderOf` — for `N = p q` and a base `a` invertible mod both factors
  with *distinct* multiplicative orders, the least exponent `M > 0` at which
  `gcd (a^M - 1) N` is a nontrivial factor is **exactly** `min (ord_p a) (ord_q a)`.  Part V
  gave the `≥` half; the `≤` half is the Xor criterion applied at `M = min`.  This is the
  first half of Conjecture 4, now a theorem, and it identifies the cost of regime (b) with an
  invariant of the *hidden* factors, invisible from `N`.
* `pm1RevealTime_demo` — an in-kernel instance: for `N = 341371 = 631 · 541` and `a = 2` the
  reveal time is exactly `45 = ord_631 2`.
-/

open CRTSplitNoGo

open Finset

/-! ## Part A: the exponential tail of the birthday product -/

variable {α : Type*} [Fintype α] [DecidableEq α]




/-- `exp (-2) ≤ 1/4`: the numerical input to the quarter-threshold. -/
lemma exp_neg_two_le_quarter : Real.exp (-2 : ℝ) ≤ 1 / 4 := by
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  have hpos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  rw [Real.exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith



/-! ## Part B: the Pollard `p-1` reveal time, exactly -/






open CRTSplitNoGo in
theorem solution(a : α) (T : ℕ) (hT : T < Fintype.card α)
    (h : 4 * Fintype.card α ≤ T * (T + 1)) :
    ((injPrefixFinset a T).card : ℝ) ≤ ((Fintype.card α : ℝ) ^ (Fintype.card α)) / 4 := by
  set n := Fintype.card α with hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hle : (2 : ℝ) ≤ (T * (T + 1) : ℝ) / (2 * n) := by
    rw [le_div_iff₀ (by positivity)]
    have : ((4 * n : ℕ) : ℝ) ≤ ((T * (T + 1) : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith
  have hmono : Real.exp (-((T * (T + 1) : ℝ) / (2 * n))) ≤ Real.exp (-2 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ n := by positivity
  calc ((injPrefixFinset a T).card : ℝ)
      ≤ Real.exp (-((T * (T + 1) : ℝ) / (2 * n))) * (n : ℝ) ^ n :=
        card_injPrefix_le_exp a T hT
    _ ≤ (1 / 4) * (n : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (le_trans hmono exp_neg_two_le_quarter) hpow
    _ = ((n : ℝ) ^ n) / 4 := by ring
