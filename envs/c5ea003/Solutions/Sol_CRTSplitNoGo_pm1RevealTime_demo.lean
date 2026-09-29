-- Prove2me | solution 1 for CRTSplitNoGo.pm1RevealTime_demo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:03:43.881629+00:00
-- url     : https://prove2.me/submissions/a9df558b-7afc-485d-8561-4e00dfc18815

-- Sol generated from Bridges/CRTSplitNoGoBirthdayTail.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail
import Theorems.Thm_CRTSplitNoGo_pm1RevealTime_eq_min_orderOf

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
set_option maxRecDepth 40000 in
theorem solution: pm1RevealTime (631 * 541) 2 = 45 := by
  have hp : Nat.Prime 631 := by norm_num
  have hq : Nat.Prime 541 := by norm_num
  have h631 : orderOf ((2 : ℤ) : ZMod 631) = 45 := by
    have : (((2 : ℤ) : ZMod 631)) = (2 : ZMod 631) := by push_cast; ring
    rw [this]
    have h1 : (2 : ZMod 631) ^ 45 = 1 := by decide
    have h2 : ∀ m ∈ Nat.properDivisors 45, (2 : ZMod 631) ^ m ≠ 1 := by decide
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h1 ?_
    intro r hr hrdvd
    have hrmem : 45 / r ∈ Nat.properDivisors 45 := by
      have hr1 : 1 < r := hr.one_lt
      have hdvd45 : (45 / r) ∣ 45 := Nat.div_dvd_of_dvd hrdvd
      refine Nat.mem_properDivisors.mpr ⟨hdvd45, ?_⟩
      exact Nat.div_lt_self (by norm_num) hr1
    exact h2 _ hrmem
  have h541 : orderOf ((2 : ℤ) : ZMod 541) = 540 := by
    have : (((2 : ℤ) : ZMod 541)) = (2 : ZMod 541) := by push_cast; ring
    rw [this]
    have h1 : (2 : ZMod 541) ^ 540 = 1 := by decide
    have h2 : ∀ m ∈ Nat.properDivisors 540, (2 : ZMod 541) ^ m ≠ 1 := by decide
    refine orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h1 ?_
    intro r hr hrdvd
    have hrmem : 540 / r ∈ Nat.properDivisors 540 := by
      have hr1 : 1 < r := hr.one_lt
      have hdvd540 : (540 / r) ∣ 540 := Nat.div_dvd_of_dvd hrdvd
      refine Nat.mem_properDivisors.mpr ⟨hdvd540, ?_⟩
      exact Nat.div_lt_self (by norm_num) hr1
    exact h2 _ hrmem
  have := pm1RevealTime_eq_min_orderOf hp hq (by norm_num) (2 : ℤ)
    (by norm_num) (by norm_num) (by rw [h631, h541]; norm_num)
  rw [this, h631, h541]
  norm_num
