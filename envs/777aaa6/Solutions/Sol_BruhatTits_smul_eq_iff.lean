-- Prove2me | solution 1 for BruhatTits.smul_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:52:37.088935+00:00
-- url     : https://prove2.me/submissions/cbd537bf-e394-4ab5-a6fb-1206b7623105

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
import Theorems.Thm_BruhatTits_smul_le_iff

set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace BruhatTits
theorem _root_.solution (g : GL ι K) (M L : Submodule R (ι → K)) :
    g • M = g • L ↔ M = L := by
  refine ⟨fun h ↦ le_antisymm ?_ ?_, by rintro rfl; rfl⟩
  rw [← smul_le_iff g]
  exact le_of_eq h
  rw [← smul_le_iff g]
  exact ge_of_eq h
end BruhatTits
