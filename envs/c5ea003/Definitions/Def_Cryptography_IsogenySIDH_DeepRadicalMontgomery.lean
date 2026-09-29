-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_DeepRadicalMontgomery
-- name    : Cryptography_IsogenySIDH_DeepRadicalMontgomery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:15:05.20118+00:00
-- url     : https://prove2.me/theorems/aa67378f-39c2-48ea-9d11-b14fb7a4c5d6
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_DeepRadicalMontgomery
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.DeepRadicalMontgomery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/DeepRadicalMontgomery.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomery
/-
# Exact fibers of the radical Montgomery 2-isogeny

This file strengthens `RadicalMontgomery` from correctness and an
`X`-coordinate fiber calculation to a classification of the complete affine
fibers away from the kernel and ramification locus.  The nontrivial point in a
fiber is the explicit deck transform

`(x,y) ↦ (x⁻¹, -(y*x⁻²))`.

The results also verify that this transform preserves the source Montgomery
curve and is an involution wherever the rational formulas are defined.
-/

namespace Cryptography.IsogenySIDH

section ExactFibers

variable {K : Type*} [Field K]

/-- The nontrivial deck transformation of the affine degree-two quotient. -/
def radicalTwoDeck (P : K × K) : K × K :=
  (P.1⁻¹, -(P.2 * P.1⁻¹ ^ 2))







end ExactFibers

end Cryptography.IsogenySIDH


