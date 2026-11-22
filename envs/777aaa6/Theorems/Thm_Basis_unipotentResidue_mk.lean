-- Prove2me | Theorems.Thm_Basis_unipotentResidue_mk
-- name    : Basis.unipotentResidue_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:22.654811+00:00
-- url     : https://prove2.me/theorems/b84b55f6-9492-4f8a-87cf-baca9a078e95
-- title:
--   Basis: unipotent Residue mk
-- statement:
--   The Basis construction uses the unipotent Residue mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L165-L201
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L165-L201

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

theorem Basis.unipotentResidue_mk [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K))
    (x : R) (y : b.toSubmodule (R := R)) :
    (b.unipotentResidue x) (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨b.transvectEquiv x y, b.transvectEquiv_apply_mem x y⟩) := by sorry
