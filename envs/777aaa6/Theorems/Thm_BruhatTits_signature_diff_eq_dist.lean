-- Prove2me | Theorems.Thm_BruhatTits_signature_diff_eq_dist
-- name    : BruhatTits.signature_diff_eq_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T10:48:15.222023+00:00
-- url     : https://prove2.me/theorems/6b43374c-c70d-4013-a453-86bbd8310cf3
-- title:
--   Bruhat Tits: signature diff eq dist
-- statement:
--   The Bruhat Tits construction uses the signature diff eq dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L271-L278
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Lattice/Distance.lean#L271-L278

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

theorem BruhatTits.signature_diff_eq_dist (M L : BruhatTits.Lattice R) :
    signature M L 0 - signature M L 1 = dist M L := by sorry
