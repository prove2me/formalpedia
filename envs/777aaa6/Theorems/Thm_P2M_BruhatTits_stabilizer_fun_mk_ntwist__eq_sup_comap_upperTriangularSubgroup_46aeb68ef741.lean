-- Prove2me | Theorems.Thm_P2M_BruhatTits_stabilizer_fun_mk_ntwist__eq_sup_comap_upperTriangularSubgroup_46aeb68ef741
-- name    : P2M_BruhatTits_stabilizer_fun_mk_ntwist__eq_sup_comap_upperTriangularSubgroup_46aeb68ef741
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:22:27.267333+00:00
-- url     : https://prove2.me/theorems/eb2780af-a27d-43cd-b9cb-07730202e1ee
-- title:
--   P2 M Bruhat Tits stabilizer fun mk ntwist  eq sup comap upper Triangular Subgroup 46aeb68ef741: P2 M Bruhat Tits stabilizer fun mk ntwist  eq sup comap upper Triangular Subgroup 46aeb68ef741
-- statement:
--   The pointwise stabilizer of `GL₂(K)` of the segment `v₀ - v₁ - ... - vₙ` is the subgroup
--   `Kˣ * Iₙ` where `Iₙ` is the subgroup of `GL₂(R)` that is upper triangular
--   modulo `ϖ ^ n`. Here the vertex `vᵢ` is the image of the lattice `(e₀, ϖ ^ i • e₁)`.
--   In particular, this shows that the stabilizer of the edge `v₀ - v₁` is `Kˣ * I₁`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L504-L512
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/GroupAction.lean#L504-L512

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

theorem P2M_BruhatTits_stabilizer_fun_mk_ntwist__eq_sup_comap_upperTriangularSubgroup_46aeb68ef741 {ϖ : R} (hϖ : Irreducible ϖ)
    (n : ℕ) :
    MulAction.stabilizer (GL (Fin 2) K)
      (fun k : Fin (n + 1) ↦
        Vertices.mk <| (Basis.ntwist₂ (Pi.basisFun K (Fin 2)) hϖ 0 k).toLattice (R := R)) =
    (embDiagonal K (Fin 2)).range ⊔
      ((upperTriangularSubgroup _ _).comap
        (map (Ideal.Quotient.mk (.span {ϖ ^ n})))).map (map R.subtype) := by sorry

alias «BruhatTits».«stabilizer_fun_mk_ntwist₂_eq_sup_comap_upperTriangularSubgroup» := P2M_BruhatTits_stabilizer_fun_mk_ntwist__eq_sup_comap_upperTriangularSubgroup_46aeb68ef741
