-- Prove2me | Theorems.Thm_BruhatTits_signatureBasisTarget_eq
-- name    : BruhatTits.signatureBasisTarget_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:48.566915+00:00
-- url     : https://prove2.me/theorems/31290221-561e-47d5-81dc-5577c88a0dc3
-- title:
--   Bruhat Tits: signature Basis Target eq
-- statement:
--   The Bruhat Tits construction uses the signature Basis Target eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L242-L245
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L242-L245

import Definitions.Def_BruhatTits_Cartan_Uniqueness
import Definitions.Def_BruhatTits_Lattice_Basic
import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Lattice_Distance
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K} [IsDiscreteValuationRing R] [IsFractionRing R K]
open Algebra BruhatTits Matrix GeneralLinearGroup
variable {k : ℕ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
open BruhatTits

theorem BruhatTits.signatureBasisTarget_eq (M L : BruhatTits.Lattice R) (i : Fin 2) :
    signatureBasisTarget M L i =
      (signatureϖ M L ^ signature M L i : K) • (signatureBasisSource M L i).val := by sorry
