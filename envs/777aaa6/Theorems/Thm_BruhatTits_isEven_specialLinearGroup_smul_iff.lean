-- Prove2me | Theorems.Thm_BruhatTits_isEven_specialLinearGroup_smul_iff
-- name    : BruhatTits.isEven_specialLinearGroup_smul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:30.435874+00:00
-- url     : https://prove2.me/theorems/179e032e-43c9-47bb-ab13-5a90cb535f19
-- title:
--   Bruhat Tits: is Even special Linear Group smul iff
-- statement:
--   The Bruhat Tits construction uses the is Even special Linear Group smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L183-L187
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L183-L187

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isEven_specialLinearGroup_smul_iff {x : Vertices R}
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : IsEven (g • x) ↔ IsEven x := by sorry
