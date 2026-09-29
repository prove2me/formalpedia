-- Prove2me | Definitions.Def_Bridges_HammingCode
-- name    : Bridges_HammingCode
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:46.58921+00:00
-- url     : https://prove2.me/theorems/a03e4e14-f9f9-4268-9c92-34f14177a582
-- title:
--   Aether Catalog definitions — Bridges_HammingCode
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.HammingCode`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/HammingCode.lean by skeleton subtraction
import Mathlib

open Finset

namespace ECOC

/-- The Hamming distance between two Boolean words. -/
def hammingDist {m : ℕ} (x y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun j => x j ≠ y j).card

/-- The coordinates on which two codewords disagree. -/
def disagreeSet {n m : ℕ} (code : Fin n → Fin m → Bool) (c c' : Fin n) :
    Finset (Fin m) :=
  Finset.univ.filter fun j => code c j ≠ code c' j

/-- Every pair of distinct codewords has Hamming distance at least `δ`. -/
def MinDistAtLeast {n m : ℕ} (code : Fin n → Fin m → Bool) (δ : ℕ) : Prop :=
  ∀ ⦃c c'⦄, c ≠ c' → δ ≤ hammingDist (code c) (code c')

/-- The codeword indexed by `c` is the unique nearest codeword to `y`. -/
def nearestUnique {n m : ℕ} (code : Fin n → Fin m → Bool)
    (y : Fin m → Bool) (c : Fin n) : Prop :=
  ∀ c', c' ≠ c → hammingDist y (code c) < hammingDist y (code c')


end ECOC


