-- Prove2me | Theorems.Thm_BruhatTits_Lattice_mapIntermediate_finrank_eq_one_of
-- name    : BruhatTits.Lattice.mapIntermediate_finrank_eq_one_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:17.990181+00:00
-- url     : https://prove2.me/theorems/97b3b7f3-adac-4c4c-9c64-33f57e4c54fd
-- title:
--   Lattice: map Intermediate finrank eq one of
-- statement:
--   The Lattice construction uses the map Intermediate finrank eq one of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L440-L461
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L440-L461

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
open Pointwise
variable [IsFractionRing R K]

theorem BruhatTits.Lattice.mapIntermediate_finrank_eq_one_of {L M : BruhatTits.Lattice R} {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < L.M)
    (h2 : ϖ • L.M < M.M) :
    Module.finrank (ResidueField R) (L.mapIntermediate M) = 1 := by sorry
