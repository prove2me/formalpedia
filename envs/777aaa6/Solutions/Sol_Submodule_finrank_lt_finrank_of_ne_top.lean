-- Prove2me | solution 1 for Submodule.finrank_lt_finrank_of_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:47:03.327484+00:00
-- url     : https://prove2.me/submissions/ffd815cd-5bf2-48ab-859d-3ea29c8bd00c

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Submodule_zero_lt_finrank_of_ne_bot
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
theorem _root_.solution (p : Submodule R M) (hp : p ≠ ⊤) :
    Module.finrank R p < Module.finrank R M := by
  obtain ⟨p', hp'⟩ := ComplementedLattice.exists_isCompl p
  rw [← Submodule.finrank_add_eq_of_isCompl hp']
  simp only [lt_add_iff_pos_right]
  apply Submodule.zero_lt_finrank_of_ne_bot
  intro hbot
  rw [hbot] at hp'
  apply hp
  exact eq_top_of_isCompl_bot hp'
end Submodule
