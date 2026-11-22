-- Prove2me | Theorems.Thm_BruhatTits_Lattice_mapIntermediate_ne_bot_of
-- name    : BruhatTits.Lattice.mapIntermediate_ne_bot_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:36.397209+00:00
-- url     : https://prove2.me/theorems/7039b03a-d3db-4432-b95f-d49f1318a51a
-- title:
--   Lattice: map Intermediate ne bot of
-- statement:
--   The Lattice construction uses the map Intermediate ne bot of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L385-L410
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L385-L410

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

theorem BruhatTits.Lattice.mapIntermediate_ne_bot_of (L M : BruhatTits.Lattice R)
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M ≤ L.M)
    (h2 : ϖ • L.M < M.M) :
    L.mapIntermediate M ≠ ⊥ := by sorry
