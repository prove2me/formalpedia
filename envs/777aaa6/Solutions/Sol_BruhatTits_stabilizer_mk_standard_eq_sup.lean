-- Prove2me | solution 1 for BruhatTits.stabilizer_mk_standard_eq_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:35:48.606182+00:00
-- url     : https://prove2.me/submissions/be314d60-d051-4a6f-85ea-3cfe5f28cab2

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_BruhatTits_stabilizer_standard_eq_range_map_subtype
import Theorems.Thm_BruhatTits_stabilizer_mk_eq_sup

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Pointwise
namespace BruhatTits
theorem _root_.solution :
    MulAction.stabilizer (GL (Fin 2) K) (Vertices.mk <| Lattice.standard R) =
      (Matrix.GeneralLinearGroup.embDiagonal K (Fin 2)).range ⊔
        (Matrix.GeneralLinearGroup.map (n := Fin 2) R.subtype).range := by
  rw [stabilizer_mk_eq_sup, stabilizer_standard_eq_range_map_subtype]
end BruhatTits
