-- Prove2me | solution 1 for CRTSplitNoGo.card_injPrefix_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:35.341738+00:00
-- url     : https://prove2.me/submissions/d303779f-6f22-4295-a0cf-4358aed7d9d2

-- Sol generated from Bridges/CRTSplitNoGoBirthdayTail.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail
import Theorems.Thm_CRTSplitNoGo_card_injPrefix

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







/-! ## Part B: the Pollard `p-1` reveal time, exactly -/






open CRTSplitNoGo in
theorem solution(a : α) (T : ℕ) (hT : T < Fintype.card α) :
    ((injPrefixFinset a T).card : ℝ)
      = (∏ i ∈ Finset.range T, (1 - ((i : ℝ) + 1) / Fintype.card α))
          * (Fintype.card α : ℝ) ^ (Fintype.card α) := by
  set n := Fintype.card α with hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [card_injPrefix a T hT]
  push_cast
  have hD : ((n - 1).descFactorial T : ℝ) = ∏ i ∈ Finset.range T, ((n : ℝ) - 1 - i) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    have hi' : i < T := Finset.mem_range.mp hi
    have h1 : i ≤ n - 1 := by omega
    have h2 : 1 ≤ n := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    ring
  have hfac : ∏ i ∈ Finset.range T, ((n : ℝ) - 1 - i)
      = (n : ℝ) ^ T * ∏ i ∈ Finset.range T, (1 - ((i : ℝ) + 1) / n) := by
    have hterm : ∀ i ∈ Finset.range T,
        ((n : ℝ) - 1 - i) = (n : ℝ) * (1 - ((i : ℝ) + 1) / n) := by
      intro i _
      field_simp
      ring
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_range]
  have hpow : (n : ℝ) ^ T * (n : ℝ) ^ (n - T) = (n : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [hD, hfac, ← hn, ← hpow]
  ring
