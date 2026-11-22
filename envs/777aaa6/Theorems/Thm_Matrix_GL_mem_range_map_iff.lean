-- Prove2me | Theorems.Thm_Matrix_GL_mem_range_map_iff
-- name    : Matrix.GL.mem_range_map_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:21.438182+00:00
-- url     : https://prove2.me/theorems/92a5f207-6091-42fe-b777-b0b72cb80681
-- title:
--   GL: mem range map iff
-- statement:
--   The GL construction uses the mem range map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L261-L277
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L261-L277

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_GL_mem_range_map_iff

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem Matrix.GL.mem_range_map_iff {R K : Type*} [CommRing R]
    [CommRing K] (f : R →+* K) (hf : Function.Injective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : GL ι K) :
    g ∈ Set.range (Matrix.GeneralLinearGroup.map f) ↔
      (∀ (i j : ι), g i j ∈ Set.range f) ∧
        ↑g.det⁻¹ ∈ Set.range f := by sorry
