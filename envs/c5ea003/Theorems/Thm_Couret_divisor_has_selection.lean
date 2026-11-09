-- Prove2me | Theorems.Thm_Couret_divisor_has_selection
-- name    : Couret.divisor_has_selection
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:45:20.758377+00:00
-- url     : https://prove2.me/theorems/6f49e1a4-39ab-4f6e-84c9-1edb7b6f45c5
-- title:
--   Every divisor of a prime-occurrence product is a selected product
-- statement:
--   Let $w$ be a finite word of natural primes, where primes are at least two and have only divisors one and themselves. Let $N$ be the product of all occurrences. For every natural divisor $d\mid N$,
--
--   $$\exists s\text{ selecting labeled occurrences of }w:\quad\prod s=d.$$
--
--   Prime occurrences may repeat; the empty word and empty selection are included.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean, lines 25–42; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc; theorem Couret.divisor_has_selection

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

theorem divisor_has_selection (w : Word Nat) (hw : w.primeFactors)
    (d : Nat) (hd : d ∣ total natProduct w) :
    ∃ s : Choice w, Choice.eval natProduct s = d := by sorry
























end Couret
