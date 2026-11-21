-- Prove2me | solution 1 for Kourovka.CentralProductPowers.iterate_central_offDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:40:53.155969+00:00
-- url     : https://prove2.me/submissions/5ab567ab-7bfd-4e1a-b071-f78d5a6823ae

import Definitions.Def_Kourovka_PathExpansion
import Definitions.Def_Kourovka_DerivedReduction
import Definitions.Def_Kourovka_CentralProductPowers
import Theorems.Thm_Kourovka_ProductHom_decompose
import Theorems.Thm_Kourovka_ProductHom_left_center
import Theorems.Thm_Kourovka_ProductHom_right_center


set_option autoImplicit true
open Kourovka Kourovka.CentralProductPowers
open ProductPaths
variable {A B : Type*} [Group A] [Group B]
namespace Kourovka.CentralProductPowers
theorem _root_.solution (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B) (n : ℕ) :
    (∀ b, (iterateHom f n (1, b)).1 ∈ Subgroup.center A) ∧
    (∀ a, (iterateHom f n (a, 1)).2 ∈ Subgroup.center B) := by
  have hA : ∀ {a : A}, a ∈ Subgroup.center A →
      (f (a, 1)).1 ∈ Subgroup.center A := fun ha =>
    ProductHom.left_center ((MonoidHom.fst A B).comp f) (Prod.fst_surjective.comp hf) ha
  have hB : ∀ {b : B}, b ∈ Subgroup.center B →
      (f (1, b)).2 ∈ Subgroup.center B := fun hb =>
    ProductHom.right_center ((MonoidHom.snd A B).comp f) (Prod.snd_surjective.comp hf) hb
  induction n with
  | zero => exact ⟨fun _ => (Subgroup.center A).one_mem,
      fun _ => (Subgroup.center B).one_mem⟩
  | succ n ih =>
      constructor
      · intro b
        change (f^[n + 1] (1, b)).1 ∈ Subgroup.center A
        rw [Function.iterate_succ_apply']
        have he := congrArg Prod.fst (ProductHom.decompose f
          (f^[n] (1, b)).1 (f^[n] (1, b)).2)
        rw [he]
        exact (Subgroup.center A).mul_mem (hA (ih.1 b)) (h12 _)
      · intro a
        change (f^[n + 1] (a, 1)).2 ∈ Subgroup.center B
        rw [Function.iterate_succ_apply']
        have he := congrArg Prod.snd (ProductHom.decompose f
          (f^[n] (a, 1)).1 (f^[n] (a, 1)).2)
        rw [he]
        exact (Subgroup.center B).mul_mem (h21 _) (hB (ih.2 a))
end Kourovka.CentralProductPowers
