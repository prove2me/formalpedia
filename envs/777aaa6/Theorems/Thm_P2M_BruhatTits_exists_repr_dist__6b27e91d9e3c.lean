-- Prove2me | Theorems.Thm_P2M_BruhatTits_exists_repr_dist__6b27e91d9e3c
-- name    : P2M_BruhatTits_exists_repr_dist__6b27e91d9e3c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:48.802177+00:00
-- url     : https://prove2.me/theorems/707727ca-ad89-4dff-9c30-408cfc8b65ff
-- title:
--   P2 M Bruhat Tits exists repr dist  6b27e91d9e3c: P2 M Bruhat Tits exists repr dist  6b27e91d9e3c
-- statement:
--   Variant of `exists_repr_dist` in terms of `Basis.twist`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L98-L108
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L98-L108

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem P2M_BruhatTits_exists_repr_dist__6b27e91d9e3c (M L : BruhatTits.Lattice R) :
    ∃ (ϖ : R) (hϖ : Irreducible ϖ) (b : Basis (Fin 2) K (Fin 2 → K))
      (f : Fin 2 → ℤ) (_ : Antitone f),
      M = b.toLattice ∧ L = (b.twist hϖ f).toLattice ∧ f 0 - f 1 = dist M L := by sorry

alias «BruhatTits».«exists_repr_dist'» := P2M_BruhatTits_exists_repr_dist__6b27e91d9e3c
