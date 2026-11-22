-- Prove2me | Theorems.Thm_BruhatTits_stabilizer_standard_eq_range_map_subtype
-- name    : BruhatTits.stabilizer_standard_eq_range_map_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:39.64598+00:00
-- url     : https://prove2.me/theorems/221b97aa-2ff9-42fd-9801-1971a388155c
-- title:
--   Bruhat Tits: stabilizer standard eq range map subtype
-- statement:
--   The stabilizer of the standard lattice of the `GL₂(K)`-action on lattices is `GL₂(R)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L193-L239
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L193-L239

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

theorem BruhatTits.stabilizer_standard_eq_range_map_subtype :
    MulAction.stabilizer (GL (Fin 2) K) (Lattice.standard R) =
      (Matrix.GeneralLinearGroup.map R.subtype).range := by sorry
