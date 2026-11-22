-- Prove2me | Theorems.Thm_P2M_Basis_unipotentResidue_apply__d6e564de5d3b
-- name    : P2M_Basis_unipotentResidue_apply__d6e564de5d3b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:11.684052+00:00
-- url     : https://prove2.me/theorems/494d20b5-ecea-4b9b-a38c-76e139408f54
-- title:
--   P2 M Basis unipotent Residue apply  d6e564de5d3b: P2 M Basis unipotent Residue apply  d6e564de5d3b
-- statement:
--   The P2 M Basis unipotent Residue apply  d6e564de5d3b construction uses the P2 M Basis unipotent Residue apply  d6e564de5d3b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L147-L151
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L147-L151

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

theorem P2M_Basis_unipotentResidue_apply__d6e564de5d3b [IsFractionRing R K]
    (b : Basis (Fin 2) K (Fin 2 → K)) (x : R) :
    (b.unipotentResidue x) (b.toQuotient' (R := R) 1) =
      x • (b.toQuotient' (R := R) 0) + (b.toQuotient' (R := R) 1) := by sorry

alias «Basis».«unipotentResidue_apply₁» := P2M_Basis_unipotentResidue_apply__d6e564de5d3b
