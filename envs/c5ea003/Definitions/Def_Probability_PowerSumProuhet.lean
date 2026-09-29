-- Prove2me | Definitions.Def_Probability_PowerSumProuhet
-- name    : Probability_PowerSumProuhet
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:40.867355+00:00
-- url     : https://prove2.me/theorems/28249720-923d-434f-bd2e-e86f9c927ab5
-- title:
--   Aether Catalog definitions — Probability_PowerSumProuhet
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PowerSumProuhet`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PowerSumProuhet.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PowerSumMinimalCollision
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

namespace PowerSumProuhet

open Multiset PowerSumMinCollision

/-- The `k`-th power sum of a multiset of naturals. -/
def powerSum (k : ℕ) (s : Multiset ℕ) : ℕ := (s.map (fun x => x ^ k)).sum




/-! ## 1. Shifting a data set: the binomial expansion of its power sums -/


/-! ## 2. The doubling lemma -/


/-! ## 3. The Prouhet–Thue–Morse pair -/

/-- The Prouhet pair of degree `K`: iterate the doubling construction from the seed
`({0}, {1})`, doubling with shift `2^(K+1)` at each step.  Concretely `(prouhet K).1` is the
set of naturals `< 2^(K+1)` with an even number of binary digits equal to `1`, and
`(prouhet K).2` its complement. -/
def prouhet : ℕ → Multiset ℕ × Multiset ℕ
  | 0 => ({0}, {1})
  | K + 1 =>
      ((prouhet K).1 + (prouhet K).2.map (fun y => y + 2 ^ (K + 1)),
       (prouhet K).2 + (prouhet K).1.map (fun y => y + 2 ^ (K + 1)))




/-! ## 4. The uniform upper bound `m(N, K) ≤ 2^K` -/







end PowerSumProuhet


