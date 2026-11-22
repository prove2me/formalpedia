-- Prove2me | Theorems.Thm_BruhatTits_signature_antitone
-- name    : BruhatTits.signature_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:47:54.582163+00:00
-- url     : https://prove2.me/theorems/93661000-f5cc-495c-b6db-e63dcf27620e
-- title:
--   Bruhat Tits: signature antitone
-- statement:
--   The Bruhat Tits construction uses the signature antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L238-L240
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L238-L240

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

theorem BruhatTits.signature_antitone (M L : BruhatTits.Lattice R) :
    Antitone (signature M L) := by sorry
