-- Prove2me | Theorems.Thm_P2M_Basis_transvectResidue_apply__d9f90c0bfc03
-- name    : P2M_Basis_transvectResidue_apply__d9f90c0bfc03
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:35.852414+00:00
-- url     : https://prove2.me/theorems/2d4006fc-9727-4471-9b27-6769a2d74238
-- title:
--   P2 M Basis transvect Residue apply  d9f90c0bfc03: P2 M Basis transvect Residue apply  d9f90c0bfc03
-- statement:
--   The P2 M Basis transvect Residue apply  d9f90c0bfc03 construction uses the P2 M Basis transvect Residue apply  d9f90c0bfc03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L135-L138
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L135-L138

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

theorem P2M_Basis_transvectResidue_apply__d9f90c0bfc03 [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectResidue x 1 = x • b.toQuotient' (R := R) 0 + b.toQuotient' (R := R) 1 := by sorry

alias «Basis».«transvectResidue_apply₁» := P2M_Basis_transvectResidue_apply__d9f90c0bfc03
