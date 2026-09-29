-- Prove2me | Definitions.Def_Bridges_PosetTheory_ArithmeticVCDimension
-- name    : Bridges_PosetTheory_ArithmeticVCDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:18.070983+00:00
-- url     : https://prove2.me/theorems/d6fd2c0c-8b79-4af5-ad43-36b0b6c365fa
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_ArithmeticVCDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.ArithmeticVCDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/ArithmeticVCDimension.lean by skeleton subtraction
import Mathlib

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

namespace ArithmeticVCDim

/-- The naive additive height of a rational number: `|numerator| + denominator`, both
taken from the reduced representation. -/
def ratArithHeight (q : ℚ) : ℕ := q.num.natAbs + q.den







end ArithmeticVCDim


