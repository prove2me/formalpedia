-- Prove2me | solution 1 for Submodule.comap_subtype_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:43:03.259193+00:00
-- url     : https://prove2.me/submissions/a4484baa-2fd9-4b9e-9dbd-219bc0cb320d

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
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace Submodule
theorem _root_.solution (I : Ideal R) (p : Submodule R M) :
    Submodule.comap p.subtype (I • p) = I • ⊤ := by
  ext x
  simp [Submodule.mem_smul_top_iff]
end Submodule
