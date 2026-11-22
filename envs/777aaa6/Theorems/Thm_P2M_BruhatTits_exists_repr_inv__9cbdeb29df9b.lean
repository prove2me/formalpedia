-- Prove2me | Theorems.Thm_P2M_BruhatTits_exists_repr_inv__9cbdeb29df9b
-- name    : P2M_BruhatTits_exists_repr_inv__9cbdeb29df9b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:23.427763+00:00
-- url     : https://prove2.me/theorems/813151d2-6bd9-43f7-9be4-7dc07d857f4b
-- title:
--   P2 M Bruhat Tits exists repr inv  9cbdeb29df9b: P2 M Bruhat Tits exists repr inv  9cbdeb29df9b
-- statement:
--   Variant of `exists_repr_inv` in terms of `Basis.ntwist₂`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L128-L133
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L128-L133

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem P2M_BruhatTits_exists_repr_inv__9cbdeb29df9b (M L : Vertices R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      ⟦b.toLattice⟧ = M ∧ ⟦(b.ntwist₂ hϖ (inv M L) 0).toLattice⟧ = L := by sorry

alias «BruhatTits».«exists_repr_inv'» := P2M_BruhatTits_exists_repr_inv__9cbdeb29df9b
