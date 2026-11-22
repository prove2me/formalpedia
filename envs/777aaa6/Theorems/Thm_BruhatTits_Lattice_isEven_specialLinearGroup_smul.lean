-- Prove2me | Theorems.Thm_BruhatTits_Lattice_isEven_specialLinearGroup_smul
-- name    : BruhatTits.Lattice.isEven_specialLinearGroup_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:46.829839+00:00
-- url     : https://prove2.me/theorems/e34c38e5-d0b1-4793-adc7-2a56af90d50e
-- title:
--   Lattice: is Even special Linear Group smul
-- statement:
--   The Lattice construction uses the is Even special Linear Group smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L158-L166
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L158-L166

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.Lattice.isEven_specialLinearGroup_smul {L : BruhatTits.Lattice R} (h : L.IsEven)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : (g • L).IsEven := by sorry
