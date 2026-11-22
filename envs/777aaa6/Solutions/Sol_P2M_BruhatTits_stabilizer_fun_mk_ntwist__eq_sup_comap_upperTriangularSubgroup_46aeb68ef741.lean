-- Prove2me | solution 1 for P2M_BruhatTits_stabilizer_fun_mk_ntwist__eq_sup_comap_upperTriangularSubgroup_46aeb68ef741
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T11:36:31.370783+00:00
-- url     : https://prove2.me/submissions/e1023f76-32a0-46da-ab74-7bb5f3d1cc9f

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
import Theorems.Thm_P2M_BruhatTits_stabilizer_fun_ntwist__eq_sup_comap_upperTriangularSubgroup_2c5b83b490d7
import Theorems.Thm_BruhatTits_stabilizer_fun_mk_eq_sup

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]
open Matrix GeneralLinearGroup
namespace BruhatTits
theorem _root_.solution {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) :
    MulAction.stabilizer (GL (Fin 2) K)
      (fun k : Fin (n + 1) ↦
        Vertices.mk <| (Basis.ntwist₂ (Pi.basisFun K (Fin 2)) hϖ 0 k).toLattice (R := R)) =
    (embDiagonal K (Fin 2)).range ⊔
      ((upperTriangularSubgroup _ _).comap
        (map (Ideal.Quotient.mk (.span {ϖ ^ n})))).map (map R.subtype) := by
  rw [stabilizer_fun_mk_eq_sup, stabilizer_fun_ntwist₂_eq_sup_comap_upperTriangularSubgroup hϖ]
end BruhatTits
