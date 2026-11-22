-- Prove2me | Theorems.Thm_P2M_Basis_transvectResidue_apply__556496910c93
-- name    : P2M_Basis_transvectResidue_apply__556496910c93
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:02.960826+00:00
-- url     : https://prove2.me/theorems/f664e070-97b2-4ead-a613-c62cc8211bc0
-- title:
--   P2 M Basis transvect Residue apply  556496910c93: P2 M Basis transvect Residue apply  556496910c93
-- statement:
--   The P2 M Basis transvect Residue apply  556496910c93 construction uses the P2 M Basis transvect Residue apply  556496910c93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L130-L133
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L130-L133

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

theorem P2M_Basis_transvectResidue_apply__556496910c93 [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    b.transvectResidue x 0 = b.toQuotient' (R := R) 0 := by sorry

alias «Basis».«transvectResidue_apply₀» := P2M_Basis_transvectResidue_apply__556496910c93
