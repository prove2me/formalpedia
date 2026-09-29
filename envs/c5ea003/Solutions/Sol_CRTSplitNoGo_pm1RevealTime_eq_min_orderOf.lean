-- Prove2me | solution 1 for CRTSplitNoGo.pm1RevealTime_eq_min_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:02:14.057199+00:00
-- url     : https://prove2.me/submissions/d9a75b6f-d55d-4c41-9d46-56cec869ea6f

-- Sol generated from Bridges/CRTSplitNoGoBirthdayTail.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGo
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail
import Theorems.Thm_CRTSplitNoGo_pollard_pm1_lower_bound
import Theorems.Thm_CRTSplitNoGo_pollard_pm1_reveal_iff

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


/-- If `a` is invertible mod the prime `p` then its multiplicative order is positive. -/
lemma orderOf_pos_of_not_dvd {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : ¬ (p : ℤ) ∣ a) :
    0 < orderOf ((a : ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hne : ((a : ZMod p)) ≠ 0 := by
    simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using ha
  exact orderOf_pos_iff.mpr (isOfFinOrder_iff_isUnit.mpr (IsUnit.mk0 _ hne))




open CRTSplitNoGo in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (a : ℤ) (hap : ¬ (p : ℤ) ∣ a) (haq : ¬ (q : ℤ) ∣ a)
    (hdiff : orderOf ((a : ZMod p)) ≠ orderOf ((a : ZMod q))) :
    pm1RevealTime (p * q) a = min (orderOf ((a : ZMod p))) (orderOf ((a : ZMod q))) := by
  set dp := orderOf ((a : ZMod p)) with hdp
  set dq := orderOf ((a : ZMod q)) with hdq
  have hdp0 : 0 < dp := orderOf_pos_of_not_dvd hp hap
  have hdq0 : 0 < dq := orderOf_pos_of_not_dvd hq haq
  -- the minimum is a reveal exponent
  have hmem : min dp dq ∈ {M : ℕ | 0 < M ∧ RevealsFactor (p * q) (a ^ M - 1)} := by
    refine ⟨lt_min hdp0 hdq0, (pollard_pm1_reveal_iff hp hq hne a (min dp dq)).mpr ?_⟩
    rcases lt_or_gt_of_ne hdiff with hlt | hlt
    · have hmin : min dp dq = dp := min_eq_left hlt.le
      left
      refine ⟨by rw [hmin], ?_⟩
      rw [hmin]
      intro hdvd
      exact absurd (Nat.le_of_dvd hdp0 hdvd) (by omega)
    · have hmin : min dp dq = dq := min_eq_right hlt.le
      right
      refine ⟨by rw [hmin], ?_⟩
      rw [hmin]
      intro hdvd
      exact absurd (Nat.le_of_dvd hdq0 hdvd) (by omega)
  refine le_antisymm (Nat.sInf_le hmem) ?_
  -- and nothing smaller is
  have hne' : {M : ℕ | 0 < M ∧ RevealsFactor (p * q) (a ^ M - 1)}.Nonempty := ⟨_, hmem⟩
  obtain ⟨hMpos, hMrev⟩ := Nat.sInf_mem hne'
  exact pollard_pm1_lower_bound hp hq hne a _ hMpos hMrev
