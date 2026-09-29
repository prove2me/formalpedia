-- Prove2me | solution 1 for PowerSumProuhet.powerSum_map_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:26:30.035488+00:00
-- url     : https://prove2.me/submissions/d40a7b03-8155-4f24-91ae-a56241b970fd

-- Sol generated from Probability/PowerSumProuhet.lean
import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
import Definitions.Def_Probability_PowerSumProuhet
import Definitions.Def_Probability_PowerSumSharpness
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



@[simp] lemma powerSum_cons (k a : ℕ) (s : Multiset ℕ) :
    powerSum k (a ::ₘ s) = a ^ k + powerSum k s := by
  simp [powerSum]


/-! ## 1. Shifting a data set: the binomial expansion of its power sums -/


/-! ## 2. The doubling lemma -/


/-! ## 3. The Prouhet–Thue–Morse pair -/





/-! ## 4. The uniform upper bound `m(N, K) ≤ 2^K` -/








open PowerSumProuhet in
theorem solution(t : Multiset ℕ) (M k : ℕ) :
    powerSum k (t.map (fun y => y + M)) =
      ∑ j ∈ Finset.range (k + 1), powerSum j t * (k.choose j * M ^ (k - j)) := by
  induction t using Multiset.induction with
  | empty => simp [powerSum]
  | cons a s ih =>
      rw [Multiset.map_cons, powerSum_cons, ih]
      have hsum : ∑ j ∈ Finset.range (k + 1), powerSum j (a ::ₘ s) * (k.choose j * M ^ (k - j))
          = (∑ j ∈ Finset.range (k + 1), a ^ j * (k.choose j * M ^ (k - j)))
            + ∑ j ∈ Finset.range (k + 1), powerSum j s * (k.choose j * M ^ (k - j)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by rw [powerSum_cons, add_mul]
      rw [hsum]
      congr 1
      rw [add_pow]
      exact Finset.sum_congr rfl fun j _ => by simp only [Nat.cast_id]; ring
