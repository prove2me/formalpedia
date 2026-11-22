-- Prove2me | Theorems.Thm_P2M_BruhatTits_exists_repr_inv__of_fixed_37640b29b3c7
-- name    : P2M_BruhatTits_exists_repr_inv__of_fixed_37640b29b3c7
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:54.506435+00:00
-- url     : https://prove2.me/theorems/63961d3f-f2af-45ec-bc1a-baecf139b304
-- title:
--   P2 M Bruhat Tits exists repr inv  of fixed 37640b29b3c7: P2 M Bruhat Tits exists repr inv  of fixed 37640b29b3c7
-- statement:
--   Variant of `exists_repr_inv_of_fixed` in terms of `Basis.ntwist₂`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L111-L125
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L111-L125

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem P2M_BruhatTits_exists_repr_inv__of_fixed_37640b29b3c7 (M : BruhatTits.Lattice R) (L : Vertices R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K)),
      b.toLattice = M ∧ ⟦(b.ntwist₂ hϖ (inv ⟦M⟧ L) 0).toLattice⟧ = L := by sorry

alias «BruhatTits».«exists_repr_inv'_of_fixed» := P2M_BruhatTits_exists_repr_inv__of_fixed_37640b29b3c7
