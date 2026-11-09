-- Prove2me | Definitions.Def_Couret_DivisorCompleteness_e4011d047800
-- name    : Couret_DivisorCompleteness_e4011d047800
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:15.908087+00:00
-- url     : https://prove2.me/theorems/3196f43f-0d62-4dc3-a85e-d139a9c65c6f
-- title:
--   Prime occurrence words
-- statement:
--   A natural number $p$ is prime here when $p\ge2$ and each natural divisor of $p$ is either one or $p$. A finite word has prime factors when every labeled occurrence satisfies this predicate, recursively from the empty word.
--
--   This interface records exactly the primality assumption needed to turn occurrence selections into all natural divisors, allowing repeated primes.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/DivisorCompleteness.lean; source file SHA-256 986d74b33e5a43fec7c07b5bec764fc731e63f4cb0c4d6d7c709dfb6dba28abc

import Std
import Definitions.Def_Couret_SupportSemantics_a8ae2832b450

/-!
COU-87 S2: exact natural-divisor semantics of a word of prime occurrences.
Primality is the elementary natural-number definition, not a completeness
assumption: p >= 2 and its divisors are exactly 1 or p.
The library theorem Nat.dvd_mul splits a divisor across a product.
-/

namespace Couret

def PrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

def Word.primeFactors : Word Nat → Prop
  | .empty => True
  | .snoc w p => w.primeFactors ∧ PrimeNat p



























end Couret


