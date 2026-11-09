-- Prove2me | Theorems.Thm_Couret_divisor_has_proper_selection
-- name    : Couret.divisor_has_proper_selection
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:51.738696+00:00
-- url     : https://prove2.me/theorems/c55145c4-ed5d-49af-9741-9c7b7654e75b
-- title:
--   A proper divisor is represented by a proper prime-factor selection
-- statement:
--   Let $w$ be a finite word of natural primes with product $N$, and let $d\mid N$ satisfy $1<d<N$. Then $$d\in\operatorname{ProperProducts}(w),$$ meaning some nonempty proper selection of positions has product $d$. Repeated prime factors are allowed.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean, lines 51–66; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc; theorem Couret.divisor_has_proper_selection

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Theorems.Thm_Couret_Choice_eval_of_not_omitted
import Theorems.Thm_Couret_Choice_eval_of_not_picked
import Theorems.Thm_Couret_divisor_has_selection
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret

theorem divisor_has_proper_selection (w : Word Nat) (hw : w.primeFactors)
    (d : Nat) (hd : d ∣ total natProduct w) (hone : 1 < d)
    (hlt : d < total natProduct w) : properSupport natProduct w d := by sorry




















end Couret
