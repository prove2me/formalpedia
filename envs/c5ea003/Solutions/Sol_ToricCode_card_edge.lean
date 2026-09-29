-- Prove2me | solution 1 for ToricCode.card_edge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:41:52.644059+00:00
-- url     : https://prove2.me/submissions/a12ae6bf-1ca8-483f-9dd0-f47bc9eae7a3

-- Sol generated from Geometry/ToricCode/Basic.lean
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

open Matrix

open ToricCode


variable (M N : ℕ) [NeZero M] [NeZero N]








/-! ### Pointwise formulas -/







/-! ### The chain condition -/




/-! ### Basic counting -/




/-! ### Kernels of the two coboundary operators are the constants -/



open ToricCode in
theorem solution: Fintype.card (Edge M N) = 2 * (M * N) := by
  simp [Fintype.card_prod, ZMod.card]
