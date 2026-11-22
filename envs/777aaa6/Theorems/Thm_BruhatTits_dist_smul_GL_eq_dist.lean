-- Prove2me | Theorems.Thm_BruhatTits_dist_smul_GL_eq_dist
-- name    : BruhatTits.dist_smul_GL_eq_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:09:55.170458+00:00
-- url     : https://prove2.me/theorems/ea842fa0-b14e-4e33-98b5-ee264f6dea8f
-- title:
--   Bruhat Tits: dist smul GL eq dist
-- statement:
--   The Bruhat Tits construction uses the dist smul GL eq dist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L164-L168
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L164-L168

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.dist_smul_GL_eq_dist (M L : BruhatTits.Lattice R) (g : GL (Fin 2) K) :
    dist (g • M) (g • L) = dist M L := by sorry
