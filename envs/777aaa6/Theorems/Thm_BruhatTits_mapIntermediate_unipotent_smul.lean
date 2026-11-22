-- Prove2me | Theorems.Thm_BruhatTits_mapIntermediate_unipotent_smul
-- name    : BruhatTits.mapIntermediate_unipotent_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:16.167812+00:00
-- url     : https://prove2.me/theorems/d39edbbd-2a45-4c17-af2a-d81a80afc38e
-- title:
--   Bruhat Tits: map Intermediate unipotent smul
-- statement:
--   The action of `b.unipotent` on lattices commutes with the projection `L` to `L ⧸ ϖ L`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L500-L541
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L500-L541

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

theorem BruhatTits.mapIntermediate_unipotent_smul (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) (M : BruhatTits.Lattice R) :
    (b.toLattice (R := R)).mapIntermediate (b.unipotent x • M) =
      ((b.toLattice (R := R)).mapIntermediate M).map (b.unipotentResidue x).toLinearMap := by sorry
