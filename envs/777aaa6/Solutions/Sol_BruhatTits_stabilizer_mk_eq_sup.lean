-- Prove2me | solution 1 for BruhatTits.stabilizer_mk_eq_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:33:59.838063+00:00
-- url     : https://prove2.me/submissions/82df6ced-8a36-4bdb-810d-f1c5c23d6d29

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_BruhatTits_stabilizer_fun_mk_eq_sup
import Theorems.Thm_MulAction_stabilizer_fun_const


set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Matrix GeneralLinearGroup
namespace BruhatTits
theorem _root_.solution (L : BruhatTits.Lattice R) :
    MulAction.stabilizer (GL (Fin 2) K) (Vertices.mk L) =
      (embDiagonal K (Fin 2)).range ⊔ MulAction.stabilizer (GL (Fin 2) K) L := by
  rw [← MulAction.stabilizer_fun_const Unit, ← MulAction.stabilizer_fun_const Unit _ L,
    stabilizer_fun_mk_eq_sup]
end BruhatTits
