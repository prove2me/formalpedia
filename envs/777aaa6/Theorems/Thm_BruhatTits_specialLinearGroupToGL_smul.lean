-- Prove2me | Theorems.Thm_BruhatTits_specialLinearGroupToGL_smul
-- name    : BruhatTits.specialLinearGroupToGL_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:54.352177+00:00
-- url     : https://prove2.me/theorems/66203eba-90eb-4af8-9a64-07d4c67d629f
-- title:
--   Bruhat Tits: special Linear Group To GL smul
-- statement:
--   The Bruhat Tits construction uses the special Linear Group To GL smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L126-L127
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L126-L127

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K

theorem BruhatTits.specialLinearGroupToGL_smul (g : Matrix.SpecialLinearGroup (Fin 2) K) (L : BruhatTits.Lattice R) :
    g.toGL • L = g • L := by sorry

attribute [defeq] BruhatTits.specialLinearGroupToGL_smul
