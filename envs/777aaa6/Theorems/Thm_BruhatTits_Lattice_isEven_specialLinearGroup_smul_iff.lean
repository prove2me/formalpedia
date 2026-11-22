-- Prove2me | Theorems.Thm_BruhatTits_Lattice_isEven_specialLinearGroup_smul_iff
-- name    : BruhatTits.Lattice.isEven_specialLinearGroup_smul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:32.033173+00:00
-- url     : https://prove2.me/theorems/b41bb27b-a4d2-47fb-b497-41a7520f4bda
-- title:
--   Lattice: is Even special Linear Group smul iff
-- statement:
--   The Lattice construction uses the is Even special Linear Group smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L169-L174
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L169-L174

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.Lattice.isEven_specialLinearGroup_smul_iff {L : BruhatTits.Lattice R}
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (g • L).IsEven ↔ L.IsEven := by sorry
