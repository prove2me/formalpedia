-- Prove2me | solution 1 for CRTSplitNoGo.average_closureTime_ge_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:34.866246+00:00
-- url     : https://prove2.me/submissions/f97b3b95-c7a9-40f2-aefe-e190bc20474f

-- Sol generated from Bridges/CRTSplitNoGoAverage.lean
import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoAverage
import Definitions.Def_Bridges_CRTSplitNoGoBirthdayTail
import Theorems.Thm_CRTSplitNoGo_average_closureTime_ge

/-!
# The CRT-Split No-Go, Part VIII: the average-case birthday barrier

Parts VI and VII count the maps whose orbit prefix is collision-free.  This file converts that
counting law into a statement about the *first closure time itself*, averaged over all maps —
the quantity that actually governs the running time of a rho-type factoring iteration.

For a map `f : α → α` and a seed `a`, `closureTime a f` is the least `T` at which the orbit
prefix `a, f a, …, f^[T] a` collides (it exists by pigeonhole, `not_injPrefix_card`).

**Main results.**

* `closureTime_spec` / `lt_closureTime_of_injPrefix` — `closureTime` is well defined and is a
  genuine first-collision time.
* `average_closureTime_ge` — for every `T` with `T (T+1) ≤ n = card α` the sum of the closure
  times over all `n ^ n` maps is at least `(T + 1) · n ^ n / 2`; equivalently, the *average*
  first closure time is at least `(T + 1)/2`.
* `average_closureTime_ge_sqrt` — taking `T + 1 = ⌊√n⌋` this gives an average first closure
  time of at least `√n / 2`: the birthday barrier holds on average, not merely with probability
  `1/2`.
* `average_closureTime_zmod` — on the reduced state space `ZMod p` of an `N`-explicit iteration
  (Fact 2), the average first closure time is at least `√p / 2`.  Since a factor of `N = p q`
  can be revealed only at a closure (Parts I–IV), a *typical* `N`-explicit iteration needs
  `≳ √p ≈ N^{1/4}/2` steps: exponential in `log N`.
-/

open CRTSplitNoGo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]











open CRTSplitNoGo in
theorem solution(a : α) :
    (Nat.sqrt (Fintype.card α) : ℝ) * ((Fintype.card α : ℝ) ^ (Fintype.card α) / 2)
      ≤ ∑ f : α → α, (closureTime a f : ℝ) := by
  set n := Fintype.card α with hn
  set s := Nat.sqrt n with hs
  have hsle : s * s ≤ n := by
    have := Nat.sqrt_le' n
    rw [← hs] at this
    nlinarith [this]
  have hsn : s ≤ n := Nat.sqrt_le_self n
  rcases Nat.eq_zero_or_pos s with hs0 | hs0
  · have : (Nat.sqrt n : ℝ) = 0 := by rw [← hs, hs0]; norm_num
    rw [this]
    have : (0 : ℝ) ≤ ∑ f : α → α, (closureTime a f : ℝ) :=
      Finset.sum_nonneg (fun f _ => by positivity)
    linarith
  · -- take `T = s - 1`
    have hTlt : s - 1 < n := by omega
    have hTmul : (s - 1) * ((s - 1) + 1) ≤ n := by
      have : (s - 1) + 1 = s := by omega
      rw [this]
      calc (s - 1) * s ≤ s * s := Nat.mul_le_mul_right s (by omega)
        _ ≤ n := hsle
    have := average_closureTime_ge a (s - 1) hTlt hTmul
    have hcast : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by
      have : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
        have : (1 : ℕ) ≤ s := hs0
        push_cast [Nat.cast_sub this]
        ring
      rw [this]; ring
    rwa [hcast] at this
