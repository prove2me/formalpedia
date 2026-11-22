-- Prove2me | Definitions.Def_BruhatTits_Utils_IsBasisOn
-- name    : BruhatTits_Utils_IsBasisOn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:43:24.752093+00:00
-- url     : https://prove2.me/theorems/cfa40976-8554-40a3-924e-070f32e0db76
-- title:
--   Is Basis On
-- statement:
--   Definitions and structural lemmas for Is Basis On, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/IsBasisOn.lean

import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Theorems.Thm_Subtype_val_comp_add
import Theorems.Thm_Subtype_val_comp_single
import Theorems.Thm_Subtype_val_comp_smul
attribute [local simp] Subtype.val_comp_add
attribute [local simp] Subtype.val_comp_single
attribute [local simp] Subtype.val_comp_smul


set_option autoImplicit false
variable {R K V ι : Type*} [CommSemiring R] [Semiring K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
class IsBasisOn (b : ι → V) (M : Submodule R V) : Prop where
  linearIndependent' : LinearIndependent R b
  span_range_eq' : Submodule.span R (Set.range b) = M
namespace IsBasisOn
variable (b : ι → V) (M : Submodule R V)
lemma linearIndependent [IsBasisOn b M] : LinearIndependent R b := linearIndependent' M
lemma span_range_eq [IsBasisOn b M] : Submodule.span R (Set.range b) = M := span_range_eq'
lemma mem [IsBasisOn b M] (i : ι) : b i ∈ M := by
  rw [← span_range_eq b M]
  apply Submodule.subset_span
  use i
def toSubmodule [IsBasisOn b M] (i : ι) : M := ⟨b i, mem b M i⟩
@[simp]
lemma toSubmodule_apply [IsBasisOn b M] (i : ι) : toSubmodule b M i = b i := rfl
lemma linearIndependent_toSubmodule [IsBasisOn b M] :
    LinearIndependent R (toSubmodule b M) := by
  rw [← M.subtype.linearIndependent_iff_of_injOn Subtype.val_injective.injOn]
  exact linearIndependent b M
lemma span_range_toSubmodule [IsBasisOn b M] :
    Submodule.span R (Set.range (toSubmodule b M)) = ⊤ := by
  apply Submodule.map_injective_of_injective M.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype]
  conv_rhs => rw [← span_range_eq b M]
  congr
  ext
  simp
instance (b : Basis ι R V) : IsBasisOn b (⊤ : Submodule R V) where
  linearIndependent' := b.linearIndependent
  span_range_eq' := b.span_eq
instance (b : Basis ι K V) [FaithfulSMul R K] : IsBasisOn b (Submodule.span R (Set.range b)) where
  linearIndependent' := b.linearIndependent.restrict_scalars' R
  span_range_eq' := rfl
instance (b : Basis ι R M) : IsBasisOn (Subtype.val ∘ b) M where
  linearIndependent' :=
    (M.subtype.linearIndependent_iff_of_injOn M.subtype_injective.injOn).mpr b.linearIndependent
  span_range_eq' := by
    conv_rhs => rw [← Submodule.range_subtype M, ← Submodule.map_top M.subtype]
    rw [Set.range_comp, ← M.coe_subtype, ← Submodule.map_span M.subtype, b.span_eq]
end IsBasisOn
open IsBasisOn
noncomputable def Basis.ofIsBasisOn (b : ι → V) (M : Submodule R V) [IsBasisOn b M] :
    Basis ι R M :=
  Basis.mk (linearIndependent_toSubmodule b M) (by rw [span_range_toSubmodule])


