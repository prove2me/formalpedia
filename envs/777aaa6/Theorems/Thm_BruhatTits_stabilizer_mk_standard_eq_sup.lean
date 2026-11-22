-- Prove2me | Theorems.Thm_BruhatTits_stabilizer_mk_standard_eq_sup
-- name    : BruhatTits.stabilizer_mk_standard_eq_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:37.413766+00:00
-- url     : https://prove2.me/theorems/1e2ba28f-532c-4489-90de-b8b0a1e11658
-- title:
--   Bruhat Tits: stabilizer mk standard eq sup
-- statement:
--   The stabilizer of the `GL₂(K)`-action on the standard vertex is `Kˣ * GL₂(R)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L491-L495
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L491-L495

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

theorem BruhatTits.stabilizer_mk_standard_eq_sup :
    MulAction.stabilizer (GL (Fin 2) K) (Vertices.mk <| Lattice.standard R) =
      (Matrix.GeneralLinearGroup.embDiagonal K (Fin 2)).range ⊔
        (Matrix.GeneralLinearGroup.map (n := Fin 2) R.subtype).range := by sorry
