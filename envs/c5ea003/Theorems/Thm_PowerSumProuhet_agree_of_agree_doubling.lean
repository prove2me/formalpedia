-- Prove2me | Theorems.Thm_PowerSumProuhet_agree_of_agree_doubling
-- name    : PowerSumProuhet.agree_of_agree_doubling
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:52:25.557026+00:00
-- url     : https://prove2.me/theorems/f4efeb14-4f18-4323-a613-48fe5d579801
-- title:
--   Prouhet's doubling lemma.
-- statement:
--   **Prouhet's doubling lemma.**  If `s` and `t` have the same power sums in all orders
--   `k ≤ K`, then the *swapped* shifted unions `s ∪ (t + M)` and `t ∪ (s + M)` have the same power
--   sums in all orders `k ≤ K + 1`, for every shift `M`.  In orders `k ≤ K` every term of the
--   binomial expansion already matches; in the new order `K + 1` all lower terms still match and
--   the two top terms `∑ s^(K+1)` and `∑ t^(K+1)` appear on opposite sides, so they cancel.
--
--   ```lean
--   theorem PowerSumProuhet.agree_of_agree_doubling{s t : Multiset ℕ} {K M : ℕ}
--       (h : ∀ k ≤ K, powerSum k s = powerSum k t) :
--       ∀ k ≤ K + 1, powerSum k (s + t.map (fun y => y + M))
--         = powerSum k (t + s.map (fun y => y + M)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PowerSumProuhet.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PowerSumProuhet.lean#L79

-- Thm stub generated from Probability/PowerSumProuhet.lean
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





/-! ## 1. Shifting a data set: the binomial expansion of its power sums -/


/-! ## 2. The doubling lemma -/

theorem PowerSumProuhet.agree_of_agree_doubling{s t : Multiset ℕ} {K M : ℕ}
    (h : ∀ k ≤ K, powerSum k s = powerSum k t) :
    ∀ k ≤ K + 1, powerSum k (s + t.map (fun y => y + M))
      = powerSum k (t + s.map (fun y => y + M)) := by sorry
