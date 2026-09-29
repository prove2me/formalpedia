-- Prove2me | Theorems.Thm_ArithmeticVCDim_ratArithHeight_inv
-- name    : ArithmeticVCDim.ratArithHeight_inv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:10:14.065436+00:00
-- url     : https://prove2.me/theorems/a0ee7b02-9232-4691-8817-0d31f3222382
-- title:
--   The height is invariant under inversion: numerator and denominator swap roles.
-- statement:
--   The height is invariant under inversion: numerator and denominator swap roles.
--
--   ```lean
--   theorem ArithmeticVCDim.ratArithHeight_inv(q : ℚ) (hq : q ≠ 0) :
--       ratArithHeight q⁻¹ = ratArithHeight q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/ArithmeticVCDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/ArithmeticVCDimension.lean#L50

-- Thm stub generated from Bridges/PosetTheory/ArithmeticVCDimension.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_ArithmeticVCDimension

/-!
# The rational arithmetic height

This module supplies the arithmetic height used by
`Bridges/TropicalAlgebra/TropicalArithmeticUltrametric.lean`.

`ratArithHeight q = |num q| + den q` is the naive additive height of a rational number in
lowest terms.  It is the basic complexity measure attached to a rational datum: the
number of bits needed to write it down, up to a constant.  The file records its
elementary properties; the *failure* of the ultrametric inequality for this height —
the reason a genuine valuation is needed instead — is proved downstream in
`TropicalArithmeticUltrametric.ratArithHeight_not_nonarchimedean`.
-/

open ArithmeticVCDim

theorem ArithmeticVCDim.ratArithHeight_inv(q : ℚ) (hq : q ≠ 0) :
    ratArithHeight q⁻¹ = ratArithHeight q := by sorry
