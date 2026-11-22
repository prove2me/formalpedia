-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.HalfspaceSplitting.not_commute_twist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:11:58.975055+00:00
-- url     : https://prove2.me/submissions/158b48ee-88b0-4f6e-b472-966a4cafb4b1

import Definitions.Def_Kourovka_Modules_ModuleRealization
import Mathlib.GroupTheory.HNNExtension
import Definitions.Def_Kourovka_Halfspaces_HalfspaceSplitting

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.HalfspaceSplitting
variable {N : Type*} [Group N]
namespace Kourovka.MetabelianEnumeration.HalfspaceSplitting
theorem _root_.solution (C : Subgroup N) {a b : N} (ha : a ∉ C) (hb : b ∉ C) :
    ¬ Commute (left C a) (right C b) := by
  intro hab
  let w : HNNExtension.NormalWord.ReducedWord N C C :=
    { head := a
      toList := [(-1, b), (1, a⁻¹), (-1, b⁻¹), (1, 1)]
      chain := by simp [List.isChain_cons_cons, HNNExtension.toSubgroup, ha, hb] }
  have hw : w.prod (MulEquiv.refl C) = 1 := by
    have hcomm : left C a * right C b * (left C a)⁻¹ * (right C b)⁻¹ = 1 :=
      (commutatorElement_eq_one_iff_commute.mpr hab)
    simpa [w, HNNExtension.NormalWord.ReducedWord.prod, left, right, MulAut.conj_apply,
      mul_assoc] using hcomm
  have hn := HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range
    (MulEquiv.refl C) w (show w.prod (MulEquiv.refl C) ∈
      (HNNExtension.of.range : Subgroup (Twist C)) by rw [hw]; exact Subgroup.one_mem _)
  simp [w] at hn
end Kourovka.MetabelianEnumeration.HalfspaceSplitting
