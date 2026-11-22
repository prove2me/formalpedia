-- Prove2me | Theorems.Thm_P2M_Basis_toQuotient__apply_64e19fe42c7f
-- name    : P2M_Basis_toQuotient__apply_64e19fe42c7f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:58.972256+00:00
-- url     : https://prove2.me/theorems/190346ee-11bc-4c69-9b5a-d4856c68cb94
-- title:
--   P2 M Basis to Quotient  apply 64e19fe42c7f: P2 M Basis to Quotient  apply 64e19fe42c7f
-- statement:
--   The P2 M Basis to Quotient  apply 64e19fe42c7f construction uses the P2 M Basis to Quotient  apply 64e19fe42c7f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L118-L122
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L118-L122

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

theorem P2M_Basis_toQuotient__apply_64e19fe42c7f [IsFractionRing R K] (b : Basis (Fin 2) K (Fin 2 → K)) (i : Fin 2) :
    b.toQuotient' (R := R) i =
      Submodule.Quotient.mk (p := (maximalIdeal R • ⊤ : Submodule R _)) (b.restrict (R := R) i) := by sorry

alias «Basis».«toQuotient'_apply» := P2M_Basis_toQuotient__apply_64e19fe42c7f
