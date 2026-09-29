-- Prove2me | Definitions.Def_Probability_PowerSumMinimalCollision
-- name    : Probability_PowerSumMinimalCollision
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:34:51.457764+00:00
-- url     : https://prove2.me/theorems/27b32ce4-c484-4b15-aeed-738b3ed4ac9a
-- title:
--   Aether Catalog definitions — Probability_PowerSumMinimalCollision
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PowerSumMinimalCollision`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PowerSumMinimalCollision.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
/-
# The minimal collision size `m(N, K)` of the finite moment problem

`Probability.PowerSumSharpness` and `Probability.PowerSumNewtonThreshold` establish the two
rigidity mechanisms for the finite moment problem on `{0, …, N}` (Vandermonde in the alphabet,
Newton in the size) together with sharpness witnesses.  This file turns those scattered bounds
into a *single numerical invariant* and computes it exactly in the cases that the previous
files bound from both sides.

For an alphabet bound `N` and an agreement order `K`, a **collision** is a pair of different
data sets `s ≠ t` of naturals bounded by `N` whose power sums agree for all orders `k ≤ K`.
Define

  `m(N, K) = minCollisionCard N K = sInf { card s | s, t is a collision }`.

Main results.

* `collisionSizes_eq_empty_of_le` / `minCollisionCard_eq_zero_iff` — collisions exist exactly
  when `K < N`, so `m(N, K) = 0` (the junk value of `sInf ∅`) precisely in the rigid regime.
* `lt_minCollisionCard` — the Prouhet–Tarry–Escott bound `K < m(N, K)` in the non-rigid regime.
* `minCollisionCard_antitone_alphabet` — `m(·, K)` is non-increasing in the alphabet: widening
  the alphabet can only make collisions cheaper.
* `minCollisionCard_critical` — **at the critical window `K = N − 1` the invariant is
  exactly `2^(N−1)`**, the largest value it can take.
* `minCollisionCard_one`, `minCollisionCard_two`, `minCollisionCard_three` — off the critical
  window the invariant collapses to the PTE floor `K + 1`: `m(N,1) = 2` for `N ≥ 2`,
  `m(N,2) = 3` for `N ≥ 4` and `m(N,3) = 4` for `N ≥ 11`.
* `minCollisionCard_strict_drop`, `minCollisionCard_two_table` — the exact drop profile at
  `K = 2`: `m(2,2) = 0`, `m(3,2) = 4`, `m(N,2) = 3` for all `N ≥ 4`.  This settles the
  `K = 2` case of sub-conjecture **S1** of `FUTURE_DIRECTIONS.md`.
* `isCollision_sub_of_isCollision`, `exists_disjoint_minimal_collision` — a collision of least
  size can always be taken *disjoint*: deleting the common part `s ∩ t` preserves agreement in
  every order and can only shrink the data sets.
-/

namespace PowerSumMinCollision

open Multiset

/-! ## 1. Collisions and the invariant `m(N, K)` -/

/-- `IsCollision N K s t` says: `s` and `t` are different data sets of naturals bounded by `N`
whose power sums agree in all orders `k ≤ K`. -/
def IsCollision (N K : ℕ) (s t : Multiset ℕ) : Prop :=
  (∀ x ∈ s, x ≤ N) ∧ (∀ x ∈ t, x ≤ N) ∧
    (∀ k ≤ K, (s.map (fun x => x ^ k)).sum = (t.map (fun x => x ^ k)).sum) ∧ s ≠ t

/-- The set of sizes of collisions with parameters `(N, K)`. -/
def collisionSizes (N K : ℕ) : Set ℕ :=
  {n | ∃ s t : Multiset ℕ, IsCollision N K s t ∧ Multiset.card s = n}

/-- `m(N, K)`: the least size of a collision over the alphabet `{0, …, N}` at agreement
order `K`.  By convention (`sInf ∅ = 0` in `ℕ`) it is `0` when no collision exists, which by
`minCollisionCard_eq_zero_iff` happens exactly in the rigid regime `N ≤ K`. -/
noncomputable def minCollisionCard (N K : ℕ) : ℕ := sInf (collisionSizes N K)

/-! ## 2. Existence and non-existence of collisions -/




/-! ## 3. General bounds on `m(N, K)` -/






/-! ## 4. The critical window `K = N - 1`: the invariant is exactly `2^(N-1)` -/



/-! ## 5. Off the critical window: the invariant collapses to the floor `K + 1` -/




/-! ## 6. The drop profile at `K = 2` -/



/-! ## 7. Minimal collisions are disjoint -/



end PowerSumMinCollision


