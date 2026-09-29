-- Prove2me | Theorems.Thm_irreducible_X4_add_X_add_one_zmod2
-- name    : irreducible_X4_add_X_add_one_zmod2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-16T20:35:25.827111+00:00
-- url     : https://prove2.me/theorems/d49f55ba-b6c5-477b-8a44-838c27f8b03e
-- title:
--   Irreducible X4 add X add one zmod2
-- statement:
--   Formal statement of `irreducible_X4_add_X_add_one_zmod2` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem irreducible_X4_add_X_add_one_zmod2:
--       Irreducible (poly_X4_X_1 (ZMod 2)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/IrreducibleTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/IrreducibleTransfer.lean#L70

-- Thm stub generated from Bridges/IrreducibleTransfer.lean
import Mathlib
import Definitions.Def_Bridges_IrreducibleTransfer
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


-- open removed: section is not a namespace

/-! ## The polynomial definition -/


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

theorem irreducible_X4_add_X_add_one_zmod2:
    Irreducible (poly_X4_X_1 (ZMod 2)) := by sorry
