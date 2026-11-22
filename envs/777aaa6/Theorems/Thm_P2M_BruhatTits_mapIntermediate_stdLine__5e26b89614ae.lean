-- Prove2me | Theorems.Thm_P2M_BruhatTits_mapIntermediate_stdLine__5e26b89614ae
-- name    : P2M_BruhatTits_mapIntermediate_stdLine__5e26b89614ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:59:14.184174+00:00
-- url     : https://prove2.me/theorems/8682c207-d2c9-4522-80c4-d168c5d5cbb0
-- title:
--   P2 M Bruhat Tits map Intermediate std Line  5e26b89614ae: P2 M Bruhat Tits map Intermediate std Line  5e26b89614ae
-- statement:
--   The image of the span of `(ϖ • b₀, b₁)` in `L ⧸ ϖ L` is the submodule generated
--   by the image of `b₁`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L289-L332
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L289-L332

import Definitions.Def_BruhatTits_Lattice_Transvect
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Definitions.Def_BruhatTits_Lattice_Quotient
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R]
open BruhatTits
set_option synthInstance.maxHeartbeats 30000
open IsLocalRing
set_option synthInstance.maxHeartbeats 50000
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 300000

theorem P2M_BruhatTits_mapIntermediate_stdLine__5e26b89614ae [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.quotientStdLine₀ hϖ = Submodule.span (ResidueField R) { b.toQuotient' (R := R) 1 } := by sorry

alias «BruhatTits».«mapIntermediate_stdLine₀» := P2M_BruhatTits_mapIntermediate_stdLine__5e26b89614ae
