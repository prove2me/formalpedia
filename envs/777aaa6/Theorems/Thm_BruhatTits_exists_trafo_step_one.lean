-- Prove2me | Theorems.Thm_BruhatTits_exists_trafo_step_one
-- name    : BruhatTits.exists_trafo_step_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:10:43.673284+00:00
-- url     : https://prove2.me/theorems/fbad02c7-ca6a-496c-8620-05165165f6c5
-- title:
--   Bruhat Tits: exists trafo step one
-- statement:
--   If `M` is a lattice, `b = (b₁, b₂)` a basis of `K^2` and `M` is a standard
--   neighbour of `b.toLattice`, there exists `g : GL₂(K)` preserving `b.toLattice` and
--   transforming `M` into the span of `(ϖ • b₁, b₂)`.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L378-L434
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L378-L434

import Definitions.Def_BruhatTits_Graph_Vertices
import Definitions.Def_BruhatTits_Lattice_Quotient
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Definitions.Def_BruhatTits_Utils_List
import Definitions.Def_BruhatTits_Graph_Edges
set_option autoImplicit false
suppress_compilation
variable {K : Type*} [Field K] {R : Subring K}
open BruhatTits
open Pointwise
open IsLocalRing
variable [IsDiscreteValuationRing R] [IsFractionRing R K]

theorem BruhatTits.exists_trafo_step_one (M : BruhatTits.Lattice R) (b : Basis (Fin 2) K (Fin 2 → K))
    {ϖ : R} (hϖ : Irreducible ϖ)
    (h1 : M.M < b.toSubmodule)
    (h2 : ϖ • b.toSubmodule < M.M) :
    ∃ (g : GL (Fin 2) K),
        g • M = (b.ntwist₂ hϖ 1 0).toLattice ∧ g • b.toLattice (R := R) = b.toLattice := by sorry
