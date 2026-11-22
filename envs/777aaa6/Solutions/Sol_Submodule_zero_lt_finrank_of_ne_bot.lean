-- Prove2me | solution 1 for Submodule.zero_lt_finrank_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:44:22.464739+00:00
-- url     : https://prove2.me/submissions/8cf4a2cb-0fa0-4a1d-a11a-d58b9e6aca98

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul



set_option autoImplicit false
variable {R M : Type*} [Field R]  [AddCommGroup M] [Module R M]
variable [Module.Free R M] [Module.Finite R M]
namespace Submodule
theorem _root_.solution (p : Submodule R M) (hp : p ≠ ⊥) :
    0 < Module.finrank R p := by
  by_contra h
  simp only [not_lt, nonpos_iff_eq_zero, finrank_eq_zero] at h
  contradiction
end Submodule
