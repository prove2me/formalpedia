-- Prove2me | Definitions.Def_Bridges_IrreducibleTransfer
-- name    : Bridges_IrreducibleTransfer
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:27:09.599498+00:00
-- url     : https://prove2.me/theorems/9a823d7f-7443-4a31-a5a9-4fce309d5a95
-- title:
--   Aether Catalog definitions — Bridges_IrreducibleTransfer
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.IrreducibleTransfer`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/IrreducibleTransfer.lean by skeleton subtraction
import Mathlib
/-
# Irreducibility Transfer: Finite Fields to Integers

This file establishes a reusable pattern for proving irreducibility of integer
polynomials by reduction to finite fields.

## Main results

* `irreducible_X4_add_X_add_one_zmod2` — X⁴ + X + 1 is irreducible over 𝔽₂
* `irreducible_X4_add_X_add_one_int` — X⁴ + X + 1 is irreducible over ℤ
* `irreducible_X4_add_X_add_one_rat` — X⁴ + X + 1 is irreducible over ℚ
* `irreducible_of_irreducible_mod_prime_monic` — reusable transfer theorem:
    monic + irreducible mod p ⟹ irreducible over ℤ

## Strategy

We use **Route 2** (modular transfer):
1. Prove X⁴ + X + 1 is irreducible over ZMod 2.
2. Apply the Gauss-style transfer: monic ℤ-polynomial irreducible mod p ⟹ irreducible over ℤ.
3. Transfer from ℤ to ℚ via the standard Gauss lemma.
-/


open Polynomial

/-! ## The polynomial definition -/

/-- The polynomial X⁴ + X + 1 over any commutative ring. -/
noncomputable abbrev poly_X4_X_1 (R : Type*) [CommRing R] : Polynomial R :=
  X ^ 4 + X + 1

/-! ## Irreducibility over 𝔽₂ -/

/-
X⁴ + X + 1 has no roots in 𝔽₂.
-/

/-
X² + X + 1 does not divide X⁴ + X + 1 over 𝔽₂.
-/

/-
X⁴ + X + 1 is irreducible over 𝔽₂.

The proof proceeds by:
1. Showing no element of 𝔽₂ is a root (ruling out linear factors).
2. Showing X² + X + 1 (the unique irreducible quadratic over 𝔽₂) does not divide it
   (ruling out quadratic factors).
3. A degree-4 polynomial with no linear or irreducible quadratic factors is irreducible.
-/

/-! ## The reusable transfer theorem -/


/-! ## Main results -/

/-
The polynomial X⁴ + X + 1 is monic over ℤ.
-/

/-
The map of X⁴ + X + 1 from ℤ to ZMod 2 equals X⁴ + X + 1 over ZMod 2.
-/


/-
**X⁴ + X + 1 is irreducible over ℚ.**

Since X⁴ + X + 1 is monic and irreducible over ℤ, it is irreducible over ℚ
by the Gauss lemma.
-/


