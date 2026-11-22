-- Prove2me | Theorems.Thm_BruhatTits_dist_twist
-- name    : BruhatTits.dist_twist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:48.060823+00:00
-- url     : https://prove2.me/theorems/987cb26f-9552-4c7b-a7fb-f6d65d24f3a1
-- title:
--   Bruhat Tits: dist twist
-- statement:
--   If `b` is a basis of `Fin 2 → K` and `f₀ ≥ f₁`, the distance of `b.toLattice` and
--   `(b.twist hϖ f).toLattice` is `f₀ - f₁`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L137-L147
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L137-L147

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.dist_twist (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    {f : Fin 2 → ℤ} (hf : Antitone f) :
    dist b.toLattice (R := R) (b.twist hϖ f).toLattice = f 0 - f 1 := by sorry
