-- Prove2me | Theorems.Thm_BruhatTits_Lattice_mem_mapIntermediate
-- name    : BruhatTits.Lattice.mem_mapIntermediate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:58:07.860804+00:00
-- url     : https://prove2.me/theorems/11c3f884-dc49-4a34-a57f-62eddb343e4a
-- title:
--   Lattice: mem map Intermediate
-- statement:
--   The Lattice construction uses the mem map Intermediate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L224-L232
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Quotient.lean#L224-L232

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

theorem BruhatTits.Lattice.mem_mapIntermediate (L M : BruhatTits.Lattice R) (x : L.quotient) :
    x ∈ L.mapIntermediate M ↔ ∃ y : L.M, y.val ∈ M.M ∧ x = L.toQuotient y := by sorry
