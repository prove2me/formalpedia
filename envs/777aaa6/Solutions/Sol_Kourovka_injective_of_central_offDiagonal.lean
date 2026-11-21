-- Prove2me | solution 1 for Kourovka.injective_of_central_offDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:37:53.387536+00:00
-- url     : https://prove2.me/submissions/6361da81-2fa1-47ec-b4d5-0c396a3d7b67

import Definitions.Def_Kourovka_Components
import Definitions.Def_Kourovka_DerivedReduction
import Theorems.Thm_Kourovka_product_kernel_le_derived
import Theorems.Thm_Kourovka_ProductHom_decompose
import Theorems.Thm_Kourovka_central_map_kills_commutator


set_option autoImplicit true
open Kourovka
variable {G A B : Type*} [Group G] [Group A] [Group B]
namespace Kourovka
theorem _root_.solution [Group.FG A] [Group.FG B]
    (f : A × B →* A × B) (hf : Function.Surjective f)
    (h12 : ∀ b, (f (1, b)).1 ∈ Subgroup.center A)
    (h21 : ∀ a, (f (a, 1)).2 ∈ Subgroup.center B)
    (h11 : Set.InjOn (fun a => (f (a, 1)).1) (commutator A))
    (h22 : Set.InjOn (fun b => (f (1, b)).2) (commutator B)) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a, b⟩ := x
  have hd := product_kernel_le_derived f hf hx
  have hA : a ∈ commutator A := hd.1
  have hB : b ∈ commutator B := hd.2
  let f12 : B →* A := (MonoidHom.fst A B).comp (ProductHom.right f)
  let f21 : A →* B := (MonoidHom.snd A B).comp (ProductHom.left f)
  have hv12 : (f (1, b)).1 = 1 := central_map_kills_commutator f12 h12 hB
  have hv21 : (f (a, 1)).2 = 1 := central_map_kills_commutator f21 h21 hA
  have hdecomp := ProductHom.decompose f a b
  have hx' : f (a, b) = 1 := hx
  have hleft : (f (a, 1)).1 = 1 := by
    have := congrArg Prod.fst hdecomp
    simp only [hx', Prod.fst_one, Prod.fst_mul, ProductHom.left_apply,
      ProductHom.right_apply, hv12, mul_one] at this
    exact this.symm
  have hright : (f (1, b)).2 = 1 := by
    have := congrArg Prod.snd hdecomp
    simp only [hx', Prod.snd_one, Prod.snd_mul, ProductHom.left_apply,
      ProductHom.right_apply, hv21, one_mul] at this
    exact this.symm
  have ha : a = 1 := h11 hA (commutator A).one_mem (by
    change (f (a, 1)).1 = (f (1 : A × B)).1
    simpa only [map_one, Prod.fst_one] using hleft)
  have hb : b = 1 := h22 hB (commutator B).one_mem (by
    change (f (1, b)).2 = (f (1 : A × B)).2
    simpa only [map_one, Prod.snd_one] using hright)
  exact Prod.ext ha hb
end Kourovka
