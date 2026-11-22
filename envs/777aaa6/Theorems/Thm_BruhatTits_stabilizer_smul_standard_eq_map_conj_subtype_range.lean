-- Prove2me | Theorems.Thm_BruhatTits_stabilizer_smul_standard_eq_map_conj_subtype_range
-- name    : BruhatTits.stabilizer_smul_standard_eq_map_conj_subtype_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:32.875855+00:00
-- url     : https://prove2.me/theorems/1347ea5d-0553-494e-af52-b19c70ee1e18
-- title:
--   Bruhat Tits: stabilizer smul standard eq map conj subtype range
-- statement:
--   The stabilizer of any lattice `g • Lattice.standard R`
--   is the conjugate `g GL₂(R) g⁻¹`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L243-L247
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L243-L247

import Definitions.Def_BruhatTits_Graph_Graph
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Graph_GroupAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
local notation "v" => ValuationRing.valuation R K
open BruhatTits
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.stabilizer_smul_standard_eq_map_conj_subtype_range (g : GL (Fin 2) K) :
    MulAction.stabilizer (GL (Fin 2) K) (g • Lattice.standard R) =
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (Matrix.GeneralLinearGroup.map R.subtype).range := by sorry
