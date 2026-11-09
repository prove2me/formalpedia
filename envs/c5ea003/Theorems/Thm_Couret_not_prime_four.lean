-- Prove2me | Theorems.Thm_Couret_not_prime_four
-- name    : Couret.not_prime_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:10.484231+00:00
-- url     : https://prove2.me/theorems/b19cbe6f-b35e-4cf6-aac0-26ef10c68df0
-- title:
--   Four is not prime
-- statement:
--   The natural number four fails the defined primality predicate: $$\neg\operatorname{PrimeNat}(4).$$
--
--   This supplies a concrete composite case for divisor completeness.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean, lines 138–141; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc; theorem Couret.not_prime_four

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

theorem not_prime_four : ¬ PrimeNat 4 := by sorry


end Couret
