-- Prove2me | Theorems.Thm_P2M_Basis_unipotentResidue_apply__346093b846ed
-- name    : P2M_Basis_unipotentResidue_apply__346093b846ed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:29.221392+00:00
-- url     : https://prove2.me/theorems/20a810db-feac-4726-a39d-89b3d657372c
-- title:
--   P2 M Basis unipotent Residue apply  346093b846ed: P2 M Basis unipotent Residue apply  346093b846ed
-- statement:
--   The P2 M Basis unipotent Residue apply  346093b846ed construction uses the P2 M Basis unipotent Residue apply  346093b846ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L153-L157
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L153-L157

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

theorem P2M_Basis_unipotentResidue_apply__346093b846ed [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (b.unipotentResidue x) (b.toQuotient' (R := R) 0) =
      (b.toQuotient' (R := R) 0) := by sorry

alias «Basis».«unipotentResidue_apply₀» := P2M_Basis_unipotentResidue_apply__346093b846ed
