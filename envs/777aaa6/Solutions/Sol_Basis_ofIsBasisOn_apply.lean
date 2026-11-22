-- Prove2me | solution 1 for Basis.ofIsBasisOn_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:13.86712+00:00
-- url     : https://prove2.me/submissions/f14e64c0-1080-4df3-a318-4d8b7abea25a

import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_BruhatTits_Utils_IsBasisOn
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul



set_option autoImplicit false
variable {R K V ι : Type*} [CommSemiring R] [Semiring K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
open IsBasisOn
namespace Basis
theorem _root_.solution (b : ι → V) (M : Submodule R V) [IsBasisOn b M] (i : ι) :
    ofIsBasisOn b M i = b i := by
  simp [ofIsBasisOn]
end Basis
