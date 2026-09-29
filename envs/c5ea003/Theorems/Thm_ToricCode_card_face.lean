-- Prove2me | Theorems.Thm_ToricCode_card_face
-- name    : ToricCode.card_face
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:31:01.635973+00:00
-- url     : https://prove2.me/theorems/356c8c46-7b10-463b-b735-1cde49cfd48f
-- title:
--   Card face
-- statement:
--   Formal statement of `ToricCode.card_face` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ToricCode.card_face: Fintype.card (Face M N) = M * N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/ToricCode/Basic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/ToricCode/Basic.lean#L161

-- Thm stub generated from Geometry/ToricCode/Basic.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic

/-!
# The `M × N` torus surface code: cellular chain complex

This file builds the *geometric* object requested by target 3 of the previous
research cycle: the cellular chain complex of the standard square-grid
cellulation of the two-dimensional torus `(ℤ/M) × (ℤ/N)`, over the binary field
`𝔽₂`.

* vertices  `Vert M N = ZMod M × ZMod N`                      (`MN` of them),
* edges     `Edge M N = Bool × ZMod M × ZMod N`               (`2MN` of them):
  the edge `(false, u)` joins `u` to `u + (1,0)`, the edge `(true, u)` joins `u`
  to `u + (0,1)`,
* faces     `Face M N = ZMod M × ZMod N`                      (`MN` of them):
  the face `f` is the unit square with corners `f, f+(1,0), f+(0,1), f+(1,1)`.

The two boundary matrices are `d1 : Vert × Edge` and `d2 : Edge × Face`.  The
main content of this file is a set of *explicit pointwise formulas* for the four
maps `d1 *ᵥ ·`, `d2 *ᵥ ·`, `d1ᵀ *ᵥ ·`, `d2ᵀ *ᵥ ·`, together with the chain
condition `d1 ∘ d2 = 0`.  Everything downstream is proved from these formulas,
never by unfolding the matrices again.
-/

-- open removed: section is not a namespace

open ToricCode


variable (M N : ℕ) [NeZero M] [NeZero N]








/-! ### Pointwise formulas -/







/-! ### The chain condition -/




/-! ### Basic counting -/

theorem ToricCode.card_face: Fintype.card (Face M N) = M * N := by sorry
