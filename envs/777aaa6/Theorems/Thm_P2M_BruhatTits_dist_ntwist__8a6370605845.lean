-- Prove2me | Theorems.Thm_P2M_BruhatTits_dist_ntwist__8a6370605845
-- name    : P2M_BruhatTits_dist_ntwist__8a6370605845
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:40.819705+00:00
-- url     : https://prove2.me/theorems/785812a9-5c57-4a44-8591-73a41e9f4a0e
-- title:
--   P2 M Bruhat Tits dist ntwist  8a6370605845: P2 M Bruhat Tits dist ntwist  8a6370605845
-- statement:
--   The P2 M Bruhat Tits dist ntwist  8a6370605845 construction uses the P2 M Bruhat Tits dist ntwist  8a6370605845 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L186-L188
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L186-L188

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem P2M_BruhatTits_dist_ntwist__8a6370605845 (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    dist (b.toLattice (R := R)) (b.ntwist₂ hϖ n 0).toLattice = n := by sorry

alias «BruhatTits».«dist_ntwist₂» := P2M_BruhatTits_dist_ntwist__8a6370605845
