-- Prove2me | Theorems.Thm_Couret_fullSupport_iff_divisor
-- name    : Couret.fullSupport_iff_divisor
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:25.807763+00:00
-- url     : https://prove2.me/theorems/1d2dd6d5-de9f-4963-a383-eb9b040c36de
-- title:
--   Prime-factor subproducts are exactly the divisors
-- statement:
--   Let $w$ be a finite word of natural primes, with total product $N$. For every natural $d$, $$d\in\operatorname{AllProducts}(w)\iff d\mid N.$$ Empty and full selections are allowed; the empty word is included.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean, lines 44–49; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc; theorem Couret.fullSupport_iff_divisor

import Definitions.Def_Couret_DivisorCompleteness_e4011d047800
import Std
import Theorems.Thm_Couret_divisor_has_selection
import Theorems.Thm_Couret_selectedProduct_dvd_total
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret

theorem fullSupport_iff_divisor (w : Word Nat) (hw : w.primeFactors) (d : Nat) :
    fullSupport natProduct w d ↔ d ∣ total natProduct w := by sorry






















end Couret
