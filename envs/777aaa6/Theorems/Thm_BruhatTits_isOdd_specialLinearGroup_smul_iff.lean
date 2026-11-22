-- Prove2me | Theorems.Thm_BruhatTits_isOdd_specialLinearGroup_smul_iff
-- name    : BruhatTits.isOdd_specialLinearGroup_smul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:25:21.348202+00:00
-- url     : https://prove2.me/theorems/62fb4c9c-ffa0-467d-b88d-3d3b4a29364f
-- title:
--   Bruhat Tits: is Odd special Linear Group smul iff
-- statement:
--   The Bruhat Tits construction uses the is Odd special Linear Group smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L189-L191
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L189-L191

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isOdd_specialLinearGroup_smul_iff {x : Vertices R}
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : IsOdd (g • x) ↔ IsOdd x := by sorry
