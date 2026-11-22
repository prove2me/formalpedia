-- Prove2me | Definitions.Def_Kourovka_Modules_CommutatorModule
-- name    : Kourovka_Modules_CommutatorModule
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:43:31.881643+00:00
-- url     : https://prove2.me/theorems/b04e4f8e-3dba-4edb-be52-0b8319ccbc08
-- title:
--   Commutator Module
-- statement:
--   Definitions and structural lemmas for Commutator Module, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/CommutatorModule.lean

import Definitions.Def_Kourovka_Presentations_PullbackPresentation
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.MonoidAlgebra.Module
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.CommutatorModule
variable {α : Type} [Fintype α]
section KernelAction
variable {E Q : Type} [Group E] [CommGroup Q]
variable (π : E →* Q) (hπ : Function.Surjective π) [IsMulCommutative π.ker]
theorem kernel_le_conjugation_kernel :
    π.ker ≤ (MulAut.conjNormal (H := π.ker)).ker := by
  intro g hg
  change MulAut.conjNormal g = 1
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  change g * a.val * g⁻¹ = a.val
  have h := congrArg Subtype.val (mul_comm (⟨g, hg⟩ : π.ker) a)
  change g * a.val = a.val * g at h
  rw [h, mul_assoc, mul_inv_cancel, mul_one]
noncomputable def quotientConjugation : Q →* MulAut π.ker :=
  (QuotientGroup.lift π.ker (MulAut.conjNormal (H := π.ker))
    (kernel_le_conjugation_kernel π)).comp
      (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.toMonoidHom
noncomputable def rightConjugation : Q →* MulAut π.ker :=
  (quotientConjugation π hπ).comp (MulEquiv.inv Q).toMonoidHom
noncomputable def rightRepresentation : Representation ℤ Q (Additive π.ker) where
  toFun q := (rightConjugation π hπ q).toAdditive.toAddMonoidHom.toIntLinearMap
  map_one' := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (rightConjugation π hπ 1 a.toMul) = a
    rw [map_one]
    rfl
  map_mul' q r := by
    apply LinearMap.ext
    intro a
    change Additive.ofMul (rightConjugation π hπ (q * r) a.toMul) =
      Additive.ofMul (rightConjugation π hπ q (rightConjugation π hπ r a.toMul))
    rw [map_mul]
    rfl
end KernelAction
end Kourovka.MetabelianEnumeration.CommutatorModule


