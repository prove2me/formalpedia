-- Prove2me | Theorems.Thm_P2M_BruhatTits_stabilizer_fun_ntwist__eq_sup_comap_upperTriangularSubgroup_2c5b83b490d7
-- name    : P2M_BruhatTits_stabilizer_fun_ntwist__eq_sup_comap_upperTriangularSubgroup_2c5b83b490d7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:23.572177+00:00
-- url     : https://prove2.me/theorems/5da78bb1-75e5-4aa0-a95f-79a323c63220
-- title:
--   P2 M Bruhat Tits stabilizer fun ntwist  eq sup comap upper Triangular Subgroup 2c5b83b490d7: P2 M Bruhat Tits stabilizer fun ntwist  eq sup comap upper Triangular Subgroup 2c5b83b490d7
-- statement:
--   The pointwise stabilizer of the chain of lattices `L₀ - L₁ - ... - Lₙ` where `Lᵢ = (e₀, ϖ ^ n • eᵢ)`
--   is the subgroup of matrices in `GL₂(R)` that are upper triangular modulo `ϖ ^ n`.
--   We express the stabilizer of the chain as the stabilizer of the function `i ↦ Lᵢ`. Here `GL₂(K)`
--   acts pointwise on pi types.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L383-L415
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L383-L415

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

theorem P2M_BruhatTits_stabilizer_fun_ntwist__eq_sup_comap_upperTriangularSubgroup_2c5b83b490d7 {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) :
    MulAction.stabilizer (GL (Fin 2) K)
      (fun k : Fin (n + 1) ↦ (Basis.ntwist₂ (Pi.basisFun K (Fin 2)) hϖ 0 k).toLattice (R := R)) =
    ((upperTriangularSubgroup _ _).comap
      (map (Ideal.Quotient.mk (.span {ϖ ^ n})))).map (map R.subtype) := by sorry

alias «BruhatTits».«stabilizer_fun_ntwist₂_eq_sup_comap_upperTriangularSubgroup» := P2M_BruhatTits_stabilizer_fun_ntwist__eq_sup_comap_upperTriangularSubgroup_2c5b83b490d7
