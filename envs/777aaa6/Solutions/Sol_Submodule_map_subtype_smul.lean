-- Prove2me | solution 1 for Submodule.map_subtype_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:44:51.268597+00:00
-- url     : https://prove2.me/submissions/09fe2000-c159-4b8e-90a2-0eb1c1b4eaf5

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
import Theorems.Thm_Submodule_comap_subtype_smul
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


attribute [local simp] Submodule.comap_subtype_smul

set_option autoImplicit false
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace Submodule
theorem _root_.solution (I : Ideal R) (p : Submodule R M) :
    Submodule.map p.subtype (I • ⊤) = I • p := by
  rw [← Submodule.comap_subtype_smul, map_comap_eq_self]
  simp only [range_subtype]
  exact smul_le_right
end Submodule
