-- Prove2me | solution 1 for IsLattice.intersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:40.266759+00:00
-- url     : https://prove2.me/submissions/460140f6-c2e3-46c6-9afd-b8e545592a18

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_Misc
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
import Definitions.Def_BruhatTits_Lattice_Basic
import Theorems.Thm_Submodule_span_eq_top_of_rank

set_option autoImplicit false
variable {K : Type*} [Field K] {R : Subring K}
open Pointwise
variable {ι : Type*}
variable [IsFractionRing R K]
variable [IsPrincipalIdealRing R] (M : Submodule R (ι → K)) [IsLattice M]
variable [Fintype ι]
namespace IsLattice
theorem _root_.solution (M N : Submodule R (ι → K)) [IsLattice M] [IsLattice N] :
    IsLattice (M ⊓ N) where
  isFG := by
    have aux : M.FG := IsLattice.isFG
    have : IsNoetherian R M := isNoetherian_of_fg_of_noetherian M aux
    have g : (M ⊓ N) ≤ M := inf_le_left
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le g
    have h: Module.Finite R ↥(M ⊓ N):= Module.IsNoetherian.finite R ↥(M ⊓ N)
    apply Module.Finite.iff_fg.mp
    exact h
  spans := by
    apply Submodule.span_eq_top_of_rank
    have h := Submodule.rank_sup_add_rank_inf_eq M N
    rw [IsLattice.rank' M, IsLattice.rank' N, IsLattice.rank'] at h
    apply Cardinal.eq_of_add_eq_add_left h
    exact Cardinal.nat_lt_aleph0 (Fintype.card ι)
end IsLattice
