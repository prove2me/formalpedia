-- Prove2me | solution 1 for IsBasisOn.iff_exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:48.320744+00:00
-- url     : https://prove2.me/submissions/442a34ca-2035-4f76-b34b-bc7f4d24d643

import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_BruhatTits_Utils_IsBasisOn
import Theorems.Thm_Basis_ofIsBasisOn_apply
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


attribute [local simp] Basis.ofIsBasisOn_apply

set_option autoImplicit false
variable {R K V ι : Type*} [CommSemiring R] [Semiring K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
open IsBasisOn
namespace IsBasisOn
theorem _root_.solution (b : ι → V) (M : Submodule R V) :
    IsBasisOn b M ↔ ∃ (bM : Basis ι R M), ∀ i, bM i = b i := by
  refine ⟨fun hb ↦ ⟨.ofIsBasisOn b M, by simp⟩, fun h ↦ ?_⟩
  obtain ⟨bM, h⟩ := h
  convert inferInstanceAs <| IsBasisOn (Subtype.val ∘ bM) M
  ext
  simp [h]
end IsBasisOn
