-- Prove2me | Theorems.Thm_BruhatTits_isOdd_iff_notEven
-- name    : BruhatTits.isOdd_iff_notEven
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:58.099726+00:00
-- url     : https://prove2.me/theorems/7735c3ed-d4ff-42e0-8209-89b95fda7a5d
-- title:
--   Bruhat Tits: is Odd iff not Even
-- statement:
--   The Bruhat Tits construction uses the is Odd iff not Even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L143-L145
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L143-L145

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isOdd_iff_notEven (x : Vertices R) : IsOdd x ↔ ¬ IsEven x := by sorry
