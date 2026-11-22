-- Prove2me | Theorems.Thm_BruhatTits_isEven_specialLinearGroup_smul
-- name    : BruhatTits.isEven_specialLinearGroup_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:39.60056+00:00
-- url     : https://prove2.me/theorems/d29e0806-18cd-4be0-b1de-c1c40e400b15
-- title:
--   Bruhat Tits: is Even special Linear Group smul
-- statement:
--   The Bruhat Tits construction uses the is Even special Linear Group smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L176-L180
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L176-L180

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isEven_specialLinearGroup_smul {x : Vertices R} (h : IsEven x)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : IsEven (g • x) := by sorry
