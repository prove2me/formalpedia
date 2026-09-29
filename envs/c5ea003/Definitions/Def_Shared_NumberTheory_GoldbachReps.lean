-- Prove2me | Definitions.Def_Shared_NumberTheory_GoldbachReps
-- name    : Shared_NumberTheory_GoldbachReps
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:04:59.395784+00:00
-- url     : https://prove2.me/theorems/6074c1b5-db19-46f8-92e5-b09cf5c213cf
-- title:
--   Aether Catalog definitions — Shared_NumberTheory_GoldbachReps
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.NumberTheory.GoldbachReps`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/NumberTheory/GoldbachReps.lean by skeleton subtraction
import Mathlib

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

namespace GoldbachReps

open Classical

noncomputable def reps (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (fun p => p ∈ A ∧ (n - p) ∈ A ∧ p ≤ n - p) (Finset.range (n + 1))).card










end GoldbachReps


