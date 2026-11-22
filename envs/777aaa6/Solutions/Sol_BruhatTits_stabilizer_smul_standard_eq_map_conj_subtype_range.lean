-- Prove2me | solution 1 for BruhatTits.stabilizer_smul_standard_eq_map_conj_subtype_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:28:06.809172+00:00
-- url     : https://prove2.me/submissions/7f54ec43-4291-499e-a206-844b541d2aec

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_BruhatTits_stabilizer_standard_eq_range_map_subtype

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
namespace BruhatTits
theorem _root_.solution (g : GL (Fin 2) K) :
    MulAction.stabilizer (GL (Fin 2) K) (g • Lattice.standard R) =
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (Matrix.GeneralLinearGroup.map R.subtype).range := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_standard_eq_range_map_subtype]
end BruhatTits
