-- Prove2me | Theorems.Thm_BruhatTits_stabilizer_mk_eq_sup
-- name    : BruhatTits.stabilizer_mk_eq_sup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:50.348269+00:00
-- url     : https://prove2.me/theorems/a966c2f6-806b-4d47-a413-8f688ca33f30
-- title:
--   Bruhat Tits: stabilizer mk eq sup
-- statement:
--   The stabilizer of the `GL₂(K)`-action on a vertex `⟦L⟧` is `Kˣ * Stab(L)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L483-L487
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L483-L487

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Matrix GeneralLinearGroup

theorem BruhatTits.stabilizer_mk_eq_sup (L : BruhatTits.Lattice R) :
    MulAction.stabilizer (GL (Fin 2) K) (Vertices.mk L) =
      (embDiagonal K (Fin 2)).range ⊔ MulAction.stabilizer (GL (Fin 2) K) L := by sorry
