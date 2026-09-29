-- Prove2me | solution 1 for PowerSumProuhet.agree_of_agree_doubling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:15:26.610662+00:00
-- url     : https://prove2.me/submissions/7cc4d110-fa35-4611-b1a1-98dc8b1c6adf

-- Sol generated from Probability/PowerSumProuhet.lean
import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
import Definitions.Def_Probability_PowerSumProuhet
import Definitions.Def_Probability_PowerSumSharpness
import Theorems.Thm_PowerSumProuhet_powerSum_map_add
/-
# Prouhet's doubling construction: the general upper bound `m(N, K) ≤ 2^K`

`Probability.PowerSumMinimalCollision` introduces the minimal collision size

  `m(N, K) = minCollisionCard N K`,

the least size of a pair of different data sets bounded by `N` whose power sums agree in all
orders `k ≤ K`, and bounds it from below by the Prouhet–Tarry–Escott floor `K < m(N, K)`.
Upper bounds were previously available only through *ad hoc* witnesses (`{0,2}` vs `{1,1}` at
`K = 1`, `{0,3,3}` vs `{1,1,4}` at `K = 2`, `{0,4,7,11}` vs `{1,2,9,10}` at `K = 3`) and
through the even/odd binomial halves at the critical window `K = N - 1`.

This file supplies the missing *uniform* upper bound, by formalising the classical
Prouhet–Thue–Morse construction:

* `powerSum_map_add` — the binomial expansion of a shifted power sum,
  `∑_{y ∈ t} (y + M)^k = ∑_{j ≤ k} (∑_{y ∈ t} y^j) · C(k,j) · M^(k-j)`.
* `agree_of_agree_doubling` — **the doubling lemma**: if `s` and `t` have equal power sums up
  to order `K`, then `s ∪ (t + M)` and `t ∪ (s + M)` have equal power sums up to order
  `K + 1`, for *every* shift `M`.  The cross terms cancel because the construction swaps the
  two sides.
* `prouhet` and `prouhet_spec` — iterating the doubling lemma from the seed `{0}` vs `{1}`
  with shifts `M = 2^(K+1)` produces, for every `K`, a collision of degree `K` with `2^K`
  elements inside the alphabet `{0, …, 2^(K+1) - 1}`.
* `minCollisionCard_le_two_pow` — hence `m(N, K) ≤ 2^K` as soon as `2^(K+1) - 1 ≤ N`.
  `minCollisionCard_le_two_pow_of_lt` upgrades this to the whole non-rigid range `K < N` by
  antitonicity in the alphabet, and together with `PowerSumMinCollision.lt_minCollisionCard`
  this sandwiches the invariant: `K < m(N, K) ≤ 2^K` (`minCollisionCard_sandwich`).
* `minCollisionCard_mono_order` — `m(N, ·)` is monotone in the agreement order.
* `minCollisionCard_critical_eq_prouhet` — at the critical window `K = N - 1` the Prouhet
  bound is *attained*: `m(N, N-1) = 2^(N-1)`, so the upper bound `2^K` cannot be improved in
  general, while `minCollisionCard_prouhet_not_tight` records that it is far from tight off
  the critical window (`m(N, 2) = 3 < 4` for `N ≥ 4`).
-/

open PowerSumProuhet

open Multiset PowerSumMinCollision




@[simp] lemma powerSum_add (k : ℕ) (s t : Multiset ℕ) :
    powerSum k (s + t) = powerSum k s + powerSum k t := by
  simp [powerSum]

/-! ## 1. Shifting a data set: the binomial expansion of its power sums -/


/-! ## 2. The doubling lemma -/


/-! ## 3. The Prouhet–Thue–Morse pair -/





/-! ## 4. The uniform upper bound `m(N, K) ≤ 2^K` -/








open PowerSumProuhet in
theorem solution{s t : Multiset ℕ} {K M : ℕ}
    (h : ∀ k ≤ K, powerSum k s = powerSum k t) :
    ∀ k ≤ K + 1, powerSum k (s + t.map (fun y => y + M))
      = powerSum k (t + s.map (fun y => y + M)) := by
  intro k hk
  rw [powerSum_add, powerSum_add, powerSum_map_add, powerSum_map_add]
  rcases Nat.lt_or_ge k (K + 1) with hlt | hge
  · have hkK : k ≤ K := by omega
    rw [h k hkK]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [h j (by simp only [Finset.mem_range] at hj; omega)]
  · have hk1 : k = K + 1 := le_antisymm hk hge
    subst hk1
    have key : ∀ j ∈ Finset.range (K + 1),
        powerSum j t * ((K + 1).choose j * M ^ (K + 1 - j))
          = powerSum j s * ((K + 1).choose j * M ^ (K + 1 - j)) := by
      intro j hj
      rw [h j (by simp only [Finset.mem_range] at hj; omega)]
    have ht_sum : ∑ j ∈ Finset.range (K + 1 + 1),
        powerSum j t * ((K + 1).choose j * M ^ (K + 1 - j))
          = (∑ j ∈ Finset.range (K + 1),
              powerSum j s * ((K + 1).choose j * M ^ (K + 1 - j))) + powerSum (K + 1) t := by
      rw [Finset.sum_range_succ, Finset.sum_congr rfl key]
      simp
    have hs_sum : ∑ j ∈ Finset.range (K + 1 + 1),
        powerSum j s * ((K + 1).choose j * M ^ (K + 1 - j))
          = (∑ j ∈ Finset.range (K + 1),
              powerSum j s * ((K + 1).choose j * M ^ (K + 1 - j))) + powerSum (K + 1) s := by
      rw [Finset.sum_range_succ]
      simp
    rw [ht_sum, hs_sum]
    omega
