-- Prove2me | Theorems.Thm_BruhatTits_pow_smul_range_eq_range_iff
-- name    : BruhatTits.pow_smul_range_eq_range_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:54.59341+00:00
-- url     : https://prove2.me/theorems/64ca37eb-7797-42fd-8fd1-364269d002bd
-- title:
--   Bruhat Tits: pow smul range eq range iff
-- statement:
--   The Bruhat Tits construction uses the pow smul range eq range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L141-L189
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L141-L189

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Pointwise

theorem BruhatTits.pow_smul_range_eq_range_iff {ι : Type*} [Finite ι] [Nonempty ι] {ϖ : R}
    (hϖ : Irreducible ϖ) (n : ℤ) :
    ϖ.val ^ n • Set.range ((Algebra.linearMap R K).compLeft ι) =
      Set.range ((Algebra.linearMap R K).compLeft ι) ↔ n = 0 := by sorry
