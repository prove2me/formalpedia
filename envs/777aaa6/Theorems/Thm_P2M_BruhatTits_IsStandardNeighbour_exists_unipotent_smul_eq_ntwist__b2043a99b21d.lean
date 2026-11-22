-- Prove2me | Theorems.Thm_P2M_BruhatTits_IsStandardNeighbour_exists_unipotent_smul_eq_ntwist__b2043a99b21d
-- name    : P2M_BruhatTits_IsStandardNeighbour_exists_unipotent_smul_eq_ntwist__b2043a99b21d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T11:11:26.848627+00:00
-- url     : https://prove2.me/theorems/0791c264-12c6-4ead-8b90-6071a5f3f750
-- title:
--   P2 M Bruhat Tits Is Standard Neighbour exists unipotent smul eq ntwist  b2043a99b21d: P2 M Bruhat Tits Is Standard Neighbour exists unipotent smul eq ntwist  b2043a99b21d
-- statement:
--   Core of induction step in `Lattice.exists_GL_smul_eq_ntwist₂_of_isSimpleChain_cons`:
--
--   If `M` is a lattice and `b` a basis of `K^2` such that
--   - `M` is a standard neighbour of the lattice spanned by `(ϖ ^ (n + 1) • b₁, b₂)`, and
--   - `M` is not equal to the lattice spanned by `(ϖ ^ n • b₁, b₂)`, then
--   there exists a unipotent matrix transforming `M` to `(ϖ ^ (n + 2) • b₁, b₂)`.
--
--   In more geometric terms, when we later apply this to a walk in the Bruhat-Tits graph,
--   the second condition requires the walk to not backtrack, i.e. to be a trail.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L447-L510
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Graph/Edges.lean#L447-L510

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

theorem P2M_BruhatTits_IsStandardNeighbour_exists_unipotent_smul_eq_ntwist__b2043a99b21d {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ)
    (M : BruhatTits.Lattice R) (b : Basis (Fin 2) K (Fin 2 → K))
    (h : IsStandardNeighbour M (b.ntwist₂ hϖ (n + 1) 0).toLattice)
    (hne : ϖ • (b.ntwist₂ hϖ n 0).toSubmodule ≠ M.M) :
    ∃ (x : R), b.unipotent (ϖ ^ (n + 1) * x) • M = (b.ntwist₂ hϖ (n + 2) 0).toLattice := by sorry

alias «BruhatTits».«IsStandardNeighbour».«exists_unipotent_smul_eq_ntwist₂» := P2M_BruhatTits_IsStandardNeighbour_exists_unipotent_smul_eq_ntwist__b2043a99b21d
