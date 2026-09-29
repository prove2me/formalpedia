-- Prove2me | Definitions.Def_MachineLearning_NumberTheory_SymmetryTransfer
-- name    : MachineLearning_NumberTheory_SymmetryTransfer
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:28.964799+00:00
-- url     : https://prove2.me/theorems/054e5f38-b372-4939-a6bc-9565b69beb33
-- title:
--   Aether Catalog definitions — MachineLearning_NumberTheory_SymmetryTransfer
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NumberTheory.SymmetryTransfer`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NumberTheory/SymmetryTransfer.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Ordered/Unordered Representation Transfer Law.
-/

/-!
# Ordered/Unordered Goldbach Witness Transfer Law

We prove the exact relationship between ordered and unordered Goldbach
witness counts via the swap symmetry.

## Main Results

* `goldbachWitnessesOrd_swap` — swap preserves ordered witnesses
* `ordered_goldbach_count_split` — the orbit decomposition formula
* `goldbachWitnessesDiag_card_le_one` — diagonal has at most one element
* `goldbachWitnessesUnord_eq_union` — unordered = strict ∪ diagonal
-/

open Finset Nat

namespace PrimeDecomp

/-- The finset of ordered pairs `(p, q)` of primes with `p + q = n`. -/
def goldbachWitnessesOrd (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n)

/-- The finset of unordered (canonical) pairs `(p, q)` with `p ≤ q`,
both prime, and `p + q = n`. -/
def goldbachWitnessesUnord (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n ∧ pq.1 ≤ pq.2)

/-- The strictly-less-than part of Goldbach witnesses. -/
def goldbachWitnessesStrict (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n ∧ pq.1 < pq.2)

/-- The diagonal part of Goldbach witnesses: pairs `(p, p)` with `p + p = n`. -/
def goldbachWitnessesDiag (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n ∧ pq.1 = pq.2)

/-- The greater-than part of Goldbach witnesses. -/
def goldbachWitnessesGt (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
    (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ pq.1 + pq.2 = n ∧ pq.2 < pq.1)

/-
Swapping coordinates preserves membership in the ordered Goldbach witness set.
-/

/-
The strict and greater-than parts are in bijection via swap.
-/

/-
The ordered witness set splits as strict + diagonal + gt.
-/

/-
**The orbit decomposition formula:** ordered = 2 * strict + diagonal.
-/

/-
The diagonal has at most one element.
-/

/-
The strict and diagonal parts are disjoint.
-/

/-
The unordered witness set equals the union of strict and diagonal parts.
-/

/-
Unordered = strict + diagonal (cardinality).
-/

end PrimeDecomp


