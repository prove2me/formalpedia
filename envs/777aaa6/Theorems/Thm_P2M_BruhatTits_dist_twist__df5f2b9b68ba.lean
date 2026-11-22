-- Prove2me | Theorems.Thm_P2M_BruhatTits_dist_twist__df5f2b9b68ba
-- name    : P2M_BruhatTits_dist_twist__df5f2b9b68ba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:30.605676+00:00
-- url     : https://prove2.me/theorems/2bf47985-920f-4a92-a141-662fa8b7be5b
-- title:
--   P2 M Bruhat Tits dist twist  df5f2b9b68ba: P2 M Bruhat Tits dist twist  df5f2b9b68ba
-- statement:
--   The P2 M Bruhat Tits dist twist  df5f2b9b68ba construction uses the P2 M Bruhat Tits dist twist  df5f2b9b68ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L170-L184
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L170-L184

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem P2M_BruhatTits_dist_twist__df5f2b9b68ba (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n m : ℤ) :
    dist b.toLattice (R := R) (b.twist₂ hϖ n m).toLattice = |n - m| := by sorry

alias «BruhatTits».«dist_twist₂» := P2M_BruhatTits_dist_twist__df5f2b9b68ba
