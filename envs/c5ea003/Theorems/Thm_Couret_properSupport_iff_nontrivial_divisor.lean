-- Prove2me | Theorems.Thm_Couret_properSupport_iff_nontrivial_divisor
-- name    : Couret.properSupport_iff_nontrivial_divisor
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:12.700429+00:00
-- url     : https://prove2.me/theorems/3671d19a-f2fd-43f1-99fe-693b76f5420a
-- title:
--   Proper prime subproducts are exactly strict nontrivial divisors
-- statement:
--   Let $w$ be a finite word of natural primes, $n$ its total product, and $d\in\mathbb N$. Then
--
--   $$d\text{ is a nonempty proper position subproduct of }w\iff d\mid n\land1<d<n.$$
--
--   The statement covers the empty and one-prime factorizations, for which neither side has witnesses.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean, lines 68–75; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc; theorem Couret.properSupport_iff_nontrivial_divisor

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Theorems.Thm_Couret_divisor_has_proper_selection
import Theorems.Thm_Couret_properSupport_is_nontrivial_divisor
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret

theorem properSupport_iff_nontrivial_divisor (w : Word Nat) (hw : w.primeFactors)
    (d : Nat) :
    properSupport natProduct w d ↔
      d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w := by sorry


















end Couret
