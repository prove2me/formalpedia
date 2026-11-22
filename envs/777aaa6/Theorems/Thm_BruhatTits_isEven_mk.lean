-- Prove2me | Theorems.Thm_BruhatTits_isEven_mk
-- name    : BruhatTits.isEven_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:23:35.778601+00:00
-- url     : https://prove2.me/theorems/9d3813e7-7e38-480b-8ad1-d2585b702e81
-- title:
--   Bruhat Tits: is Even mk
-- statement:
--   The Bruhat Tits construction uses the is Even mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L148-L148
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Orientation.lean#L148-L148

import Definitions.Def_BruhatTits_Graph_GroupAction
import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_BruhatTits_Graph_Orientation
set_option autoImplicit false
suppress_compilation
open BruhatTits
variable {K : Type*} [Field K] {R : Subring K}
local notation "v" => ValuationRing.valuation R K
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.isEven_mk (L : BruhatTits.Lattice R) : IsEven ⟦L⟧ ↔ L.IsEven := by sorry
