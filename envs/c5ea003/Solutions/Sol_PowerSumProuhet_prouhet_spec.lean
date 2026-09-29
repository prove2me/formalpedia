-- Prove2me | solution 1 for PowerSumProuhet.prouhet_spec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:38.361474+00:00
-- url     : https://prove2.me/submissions/393b18f2-ad17-4611-860b-f6cb3226629c

-- Sol generated from Probability/PowerSumProuhet.lean
import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
import Definitions.Def_Probability_PowerSumProuhet
import Definitions.Def_Probability_PowerSumSharpness
import Theorems.Thm_PowerSumProuhet_agree_of_agree_doubling
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





/-! ## 1. Shifting a data set: the binomial expansion of its power sums -/


/-! ## 2. The doubling lemma -/


/-! ## 3. The Prouhet–Thue–Morse pair -/





/-! ## 4. The uniform upper bound `m(N, K) ≤ 2^K` -/








open PowerSumProuhet in
theorem solution(K : ℕ) :
    (∀ x ∈ (prouhet K).1, x < 2 ^ (K + 1)) ∧
    (∀ x ∈ (prouhet K).2, x < 2 ^ (K + 1)) ∧
    (∀ k ≤ K, powerSum k (prouhet K).1 = powerSum k (prouhet K).2) ∧
    Multiset.card (prouhet K).1 = 2 ^ K ∧ Multiset.card (prouhet K).2 = 2 ^ K ∧
    (0 : ℕ) ∈ (prouhet K).1 ∧ (0 : ℕ) ∉ (prouhet K).2 := by
  induction K with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [prouhet, powerSum]
  | succ K ih =>
      obtain ⟨hs, ht, hagree, hcs, hct, h0s, h0t⟩ := ih
      have hM : (0 : ℕ) < 2 ^ (K + 1) := Nat.two_pow_pos _
      have hpow : 2 ^ (K + 1) + 2 ^ (K + 1) = 2 ^ (K + 2) := by ring
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        simp only [prouhet, Multiset.mem_add, Multiset.mem_map] at hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact lt_of_lt_of_le (hs x hx) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · have := ht y hy; omega
      · intro x hx
        simp only [prouhet, Multiset.mem_add, Multiset.mem_map] at hx
        rcases hx with hx | ⟨y, hy, rfl⟩
        · exact lt_of_lt_of_le (ht x hx) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · have := hs y hy; omega
      · exact agree_of_agree_doubling hagree
      · simp [prouhet, hcs, hct, pow_succ]; ring
      · simp [prouhet, hcs, hct, pow_succ]; ring
      · simp only [prouhet, Multiset.mem_add]
        exact Or.inl h0s
      · simp only [prouhet, Multiset.mem_add, Multiset.mem_map, not_or]
        refine ⟨h0t, ?_⟩
        rintro ⟨y, -, hy⟩
        omega
