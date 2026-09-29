-- Prove2me | Definitions.Def_Applications_Combinatorics_FangMultiset
-- name    : Applications_Combinatorics_FangMultiset
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:27.797532+00:00
-- url     : https://prove2.me/theorems/34cdef68-388a-4d80-a27d-4d4d2e558270
-- title:
--   Aether Catalog definitions — Applications_Combinatorics_FangMultiset
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Combinatorics.FangMultiset`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Combinatorics/FangMultiset.lean by skeleton subtraction
import Mathlib

/-!
# The Digit-Multiset Framework for Vampire Numbers (Foundations)

A *vampire number* is a number `v` that factors as `v = x * y`, where the two
"fangs" `x` and `y` together use *exactly the same multiset of digits* as `v`
(the smallest is `1260 = 21 * 60`).  The natural home for the "same digits"
condition is the *multiset* of base-`10` digits, and this file develops that
framework **from first principles**, taking care to avoid any circular reasoning.

## Design: no circular dependencies

The literature (and the companion catalog files) often derive the digit-sum
*additivity* of a fang factorisation from the "casting out nines" congruence, or
vice-versa.  Here we keep the two ideas strictly separate:

* The purely *combinatorial* facts — that the digit sum and the digit length are
  the `Multiset.sum` and `Multiset.card` of the digit multiset, and that these
  are additive across a fang pair — are proved here using **only** multiset
  arithmetic (`Multiset.sum` and `Multiset.card` are monoid homomorphisms).  No
  congruence (`Nat.ModEq`, casting out nines, `ZMod`, …) is used anywhere in this
  file.

* The mod-`9` and mod-`3` *congruences* are derived, as downstream
  *consequences* of the additivity results, in the separate file
  `Novelty.FangCongruence`.

## Main definitions

* `FangMultiset.multiset_of_digits n` — the multiset of base-`10` digits of `n`.
* `FangMultiset.digitsum n` — the sum of the base-`10` digits of `n`.
* `FangMultiset.len n` — the number of base-`10` digits of `n`.
* `FangMultiset.IsFangPair v x y` — the fang relation: the digit multisets satisfy
  `multiset_of_digits v = multiset_of_digits x + multiset_of_digits y`, and
  `x * y = v`.

## Main results

* `FangMultiset.digitsum_eq_multiset_sum` (**Lemma 1**):
  `digitsum n = (multiset_of_digits n).sum`.
* `FangMultiset.len_eq_multiset_card` (**Lemma 2**):
  `len n = (multiset_of_digits n).card`.
* `FangMultiset.IsFangPair.digitsum_add`: `digitsum x + digitsum y = digitsum v`.
* `FangMultiset.IsFangPair.len_add`: `len v = len x + len y`.

The catalog's verified vampire results (`Bestiary.IsFangPair` in
`Novelty.VampireNumbers`, `NumericalMonsters.SharesAllDigits` in the
`output-final_aristotle` NumericalMonsters files) phrase the fang relation as a
*list permutation* `(digits v).Perm (digits x ++ digits y)`.  For continuity we
record `FangMultiset.isFangPair_iff_perm`, showing our multiset formulation is
literally equivalent to that permutation condition (via `Multiset.coe_eq_coe`).
-/

namespace FangMultiset

/-- The **multiset of base-`10` digits** of `n`.  This is the digit list
`Nat.digits 10 n` viewed as a multiset (i.e. up to reordering), which is the
right structure for the "uses the same digits" condition of vampire numbers. -/
def multiset_of_digits (n : ℕ) : Multiset ℕ := (Nat.digits 10 n : Multiset ℕ)

/-- The **digit sum** of `n` in base `10`. -/
def digitsum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- The **number of decimal digits** of `n`. -/
def len (n : ℕ) : ℕ := (Nat.digits 10 n).length



/-- The **fang relation**.  `x` and `y` are the fangs of `v` when their digit
multisets combine to that of `v` and their product is `v`:
`multiset_of_digits v = multiset_of_digits x + multiset_of_digits y` and
`x * y = v`.  (Here `+` is multiset union-with-multiplicity, the natural
counterpart of concatenating the two digit lists.) -/
def IsFangPair (v x y : ℕ) : Prop :=
  multiset_of_digits v = multiset_of_digits x + multiset_of_digits y ∧ x * y = v




/-! ### Non-vacuity: the smallest vampire number `1260 = 21 * 60`. -/

end FangMultiset


