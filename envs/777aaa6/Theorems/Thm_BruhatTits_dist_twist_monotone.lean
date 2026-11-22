-- Prove2me | Theorems.Thm_BruhatTits_dist_twist_monotone
-- name    : BruhatTits.dist_twist_monotone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:08:30.492421+00:00
-- url     : https://prove2.me/theorems/14300e9e-5573-4c38-863c-37166deb1eb8
-- title:
--   Bruhat Tits: dist twist monotone
-- statement:
--   If `b` is a basis of `Fin 2 → K` and `f₀ ≤ f₁`, the distance of `b.toLattice` and
--   `(b.twist hϖ f).toLattice` is `f₁ - f₀`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L151-L161
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Vertices.lean#L151-L161

import Definitions.Def_BruhatTits_Lattice_Distance
import Definitions.Def_BruhatTits_Lattice_Construction
import Definitions.Def_BruhatTits_Graph_Vertices
set_option autoImplicit false
open BruhatTits
variable {K : Type*} [Field K] (R : Subring K) [IsDiscreteValuationRing R]
  [IsFractionRing R K]
variable {R}
open Pointwise

theorem BruhatTits.dist_twist_monotone (b : Basis (Fin 2) K (Fin 2 → K)) {ϖ : R} (hϖ : Irreducible ϖ)
    {f : Fin 2 → ℤ} (hf : Monotone f) :
    dist b.toLattice (R := R) (b.twist hϖ f).toLattice = f 1 - f 0 := by sorry
