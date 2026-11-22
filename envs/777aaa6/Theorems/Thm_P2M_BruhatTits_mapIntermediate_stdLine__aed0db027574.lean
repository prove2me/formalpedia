-- Prove2me | Theorems.Thm_P2M_BruhatTits_mapIntermediate_stdLine__aed0db027574
-- name    : P2M_BruhatTits_mapIntermediate_stdLine__aed0db027574
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:54.447948+00:00
-- url     : https://prove2.me/theorems/f178e325-c07c-431b-ad2f-4bf13515a020
-- title:
--   P2 M Bruhat Tits map Intermediate std Line  aed0db027574: P2 M Bruhat Tits map Intermediate std Line  aed0db027574
-- statement:
--   The image of the span of `(b₀, ϖ • b₁)` in `L ⧸ ϖ L` is the submodule generated
--   by the image of `b₀`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L337-L381
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L337-L381

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
set_option synthInstance.maxHeartbeats 100000

theorem P2M_BruhatTits_mapIntermediate_stdLine__aed0db027574 [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ) :
    b.quotientStdLine₁ hϖ = Submodule.span (ResidueField R) { b.toQuotient' (R := R) 0 } := by sorry

alias «BruhatTits».«mapIntermediate_stdLine₁» := P2M_BruhatTits_mapIntermediate_stdLine__aed0db027574
