-- Prove2me | Theorems.Thm_BruhatTits_Lattice_mapIntermediate_ne_top_of
-- name    : BruhatTits.Lattice.mapIntermediate_ne_top_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:05.060556+00:00
-- url     : https://prove2.me/theorems/77980c45-095e-4258-bf29-3cb8e996bd57
-- title:
--   Lattice: map Intermediate ne top of
-- statement:
--   The Lattice construction uses the map Intermediate ne top of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L412-L436
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L412-L436

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

theorem BruhatTits.Lattice.mapIntermediate_ne_top_of (L M : BruhatTits.Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ) (h1 : M.M < L.M) (h2 : ϖ • L.M ≤ M.M) :
    L.mapIntermediate M ≠ ⊤ := by sorry
