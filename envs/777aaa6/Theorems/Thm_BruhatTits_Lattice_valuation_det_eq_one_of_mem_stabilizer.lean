-- Prove2me | Theorems.Thm_BruhatTits_Lattice_valuation_det_eq_one_of_mem_stabilizer
-- name    : BruhatTits.Lattice.valuation_det_eq_one_of_mem_stabilizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:34.558362+00:00
-- url     : https://prove2.me/theorems/2b9c1275-bae2-4a1d-8156-6b0174cf21b1
-- title:
--   Lattice: valuation det eq one of mem stabilizer
-- statement:
--   The Lattice construction uses the valuation det eq one of mem stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L249-L259
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L249-L259

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.Lattice.valuation_det_eq_one_of_mem_stabilizer (L : BruhatTits.Lattice R) (g : GL (Fin 2) K)
      (hg : g ∈ MulAction.stabilizer _ L) :
    v g.det = 1 := by sorry
