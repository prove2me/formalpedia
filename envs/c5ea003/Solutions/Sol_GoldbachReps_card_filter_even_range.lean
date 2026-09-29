-- Prove2me | solution 1 for GoldbachReps.card_filter_even_range
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:18:49.307349+00:00
-- url     : https://prove2.me/submissions/9487ecff-10d4-465f-904e-3cd2428fa33a

-- Sol generated from Shared/NumberTheory/GoldbachReps.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_GoldbachReps

/-!
# Combinatorial properties of the Goldbach representation counter

This file defines a representation counter `reps A n`, counting the number of
*unordered* representations `n = p + q` with `p, q ∈ A` (encoded by `p ≤ n - p`),
and proves several structural results about it.

The headline result is `reps_symmetric_eq`: if a set `A` is symmetric about `n/2`
(closed under `k ↦ n - k` on its elements `≤ n`), then `reps A n` simply counts the
elements of `A` in the lower half `{0, …, ⌊n/2⌋}`.  From it we derive the value for the
full set, an upper bound valid for every set, and the exact value for the set of even
numbers.

All core arguments are explicit Finset manipulations (`Finset.ext`, `Finset.card_nbij'`,
`Finset.card_le_card`, `Finset.filter_eq_empty_iff`), with arithmetic discharged by
`omega`; no `aesop`/`grind` is used.
-/

open GoldbachReps

open Classical












open GoldbachReps in
lemma solution(M : ℕ) :
    (Finset.filter (fun p => Even p) (Finset.range (M + 1))).card = M / 2 + 1 := by
  rw [← Finset.card_range (M / 2 + 1)]
  refine Finset.card_nbij' (fun p => p / 2) (fun i => 2 * i) ?_ ?_ ?_ ?_
  · -- forward map lands in `range (M/2+1)`
    intro p hp
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Nat.even_iff] at hp
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  · -- inverse map lands in the filtered set
    intro i hi
    simp only [Finset.coe_range, Set.mem_Iio] at hi
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Nat.even_iff]
    omega
  · -- left inverse on the filtered set: `2 * (p / 2) = p` since `p` is even
    intro p hp
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq, Nat.even_iff] at hp
    show 2 * (p / 2) = p
    omega
  · -- right inverse on `range (M/2+1)`: `(2 * i) / 2 = i`
    intro i _
    show (2 * i) / 2 = i
    omega
