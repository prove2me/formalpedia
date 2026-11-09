-- Prove2me | Theorems.Thm_Couret_singleton_four_counterexample
-- name    : Couret.singleton_four_counterexample
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:19.103179+00:00
-- url     : https://prove2.me/theorems/fd0804e1-6c8e-4d16-b70a-312d51dbd3ea
-- title:
--   A composite occurrence need not realize all divisors
-- statement:
--   For the one-occurrence natural word $(4)$,
--
--   $$2\mid\prod(4),\qquad 2\text{ is not a product of a selection of its occurrences}.$$
--
--   The only selection products are one and four. This shows why prime-occurrence hypotheses are needed for divisor completeness.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean, lines 122–136; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc; theorem Couret.singleton_four_counterexample

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret

theorem singleton_four_counterexample :
    2 ∣ total natProduct (.snoc .empty 4) ∧
      ¬ fullSupport natProduct (.snoc .empty 4) 2 := by sorry




end Couret
