-- Prove2me | Definitions.Def_Couret_MixedGeometry_fb699ea460d2
-- name    : Couret_MixedGeometry_fb699ea460d2
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:56.734199+00:00
-- url     : https://prove2.me/theorems/35ef4cd3-1757-4082-af00-eabf955e8e4d
-- title:
--   Mixed antipodal geometry of four-support collisions
-- statement:
--   This bundle supplies lemmas about supports containing antipodal pairs, splitting three-element exclusive parts, and completing the opposite mixed part under half-turn stability. It also reconstructs a support from its singleton intersection and its exclusive part.
--
--   Its cyclic application rules out intersection size one for equal-square four-supports in $\mathbb Z/(2m)\mathbb Z$ when $m>0$. These results implement the mixed branch of the four-support overlap analysis.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/MixedGeometry.lean; source file SHA-256 59d78d29306c10a756d321393c071d5faf74789b4364a5fe0a7d2a8af11f3c63

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_MixedAlgebra_6992a070e438

set_option autoImplicit false
namespace Couret.InterIA.Mixed
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem fibre_closed (h a x : G) (hh2 : h+h=0) (hx : x ∈ fibre h a) :
    x+h ∈ fibre h a := by
  rw [← fibre_eq_of_mem h a x hh2 hx]
  simp [fibre]

theorem split_three_with_pair (U : Finset G) (a h : G) (hh : h ≠ 0)
    (hU : U.card=3) (ha : a ∈ U) (hah : a+h ∈ U) :
    ∃ q, q ∉ fibre h a ∧ U=insert q (fibre h a) := by
  have hsub : fibre h a ⊆ U := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact ha
    · exact Finset.mem_singleton.mp hx ▸ hah
  have hcount := Finset.card_sdiff_add_card_eq_card hsub
  have hpair := fibre_card h a hh
  have hrest : (U \ fibre h a).card=1 := by omega
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hrest
  have hqmem : q ∈ U ∧ q ∉ fibre h a := Finset.mem_sdiff.mp (by rw [hq]; simp)
  refine ⟨q,hqmem.2,?_⟩
  ext x
  constructor
  · intro hx
    by_cases hp : x ∈ fibre h a
    · exact Finset.mem_insert.mpr (Or.inr hp)
    · have hr : x ∈ U \ fibre h a := Finset.mem_sdiff.mpr ⟨hx,hp⟩
      rw [hq] at hr
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hr))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hqmem.1
    · exact hsub hx

theorem nonpure_has_pair (U V : Finset G) (h : G)
    (hcard : U.card=V.card)
    (hstable : ∀ x ∈ U ∪ V, x+h ∈ U ∪ V)
    (hnpure : V ≠ U.image (fun x => x+h)) : ∃ a ∈ U, a+h ∈ U := by
  classical
  by_contra hn
  have hno : ∀ a ∈ U, a+h ∉ U := by
    intro a ha hah
    exact hn ⟨a,ha,hah⟩
  have hsub : U.image (fun x => x+h) ⊆ V := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_union.mp (hstable a (Finset.mem_union.mpr (Or.inl ha)))).resolve_left
      (hno a ha)
  have he : U.image (fun x => x+h)=V := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ (fun x y he => add_right_cancel he),hcard]
  exact hnpure he.symm

theorem complete_mixed_target (U V : Finset G) (a q h : G)
    (hh : h ≠ 0) (hh2 : h+h=0) (hV : V.card=3)
    (hdis : Disjoint U V) (hU : U=insert q (fibre h a)) (hq : q ∉ fibre h a)
    (hstable : ∀ x ∈ U ∪ V, x+h ∈ U ∪ V) :
    ∃ b, q+h ∉ fibre h b ∧ V=insert (q+h) (fibre h b) := by
  have hqU : q ∈ U := by rw [hU]; simp
  have hqnot : q+h ∉ U := by
    intro hx
    rw [hU] at hx
    rcases Finset.mem_insert.mp hx with hx|hx
    · exact hh (add_left_cancel (by simpa using hx : q+h=q+0))
    · have hy := fibre_closed h a (q+h) hh2 hx
      exact hq (by simpa only [add_assoc,hh2,add_zero] using hy)
  have hqhV : q+h ∈ V :=
    (Finset.mem_union.mp (hstable q (Finset.mem_union.mpr (Or.inl hqU)))).resolve_left hqnot
  have hcross : ∀ x ∈ V, x+h ∈ U → x=q+h := by
    intro x hxV hxU
    rw [hU] at hxU
    rcases Finset.mem_insert.mp hxU with hx|hx
    · calc x=(x+h)+h := by rw [add_assoc,hh2,add_zero]
           _=q+h := by rw [hx]
    · have hp := fibre_closed h a (x+h) hh2 hx
      have hxP : x ∈ fibre h a := by simpa only [add_assoc,hh2,add_zero] using hp
      have hxU : x ∈ U := by rw [hU]; exact Finset.mem_insert.mpr (Or.inr hxP)
      exact False.elim (Finset.disjoint_left.mp hdis hxU hxV)
  let W := V.erase (q+h)
  have hW : W.card=2 := by
    dsimp [W]
    rw [Finset.card_erase_of_mem hqhV,hV]
  have hWstable : ∀ x ∈ W, x+h ∈ W := by
    intro x hx
    have hxe : x ≠ q+h := (Finset.mem_erase.mp hx).1
    have hxV : x ∈ V := (Finset.mem_erase.mp hx).2
    have hxhV : x+h ∈ V :=
      (Finset.mem_union.mp (hstable x (Finset.mem_union.mpr (Or.inr hxV)))).resolve_left
        (fun hxU => hxe (hcross x hxV hxU))
    have hxq : x ≠ q := by
      intro he
      exact Finset.disjoint_left.mp hdis (by simpa only [he] using hqU) hxV
    exact Finset.mem_erase.mpr ⟨fun he => hxq (add_right_cancel he),hxhV⟩
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (by omega : 0 < W.card)
  have hsub : fibre h b ⊆ W := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hb
    · exact Finset.mem_singleton.mp hx ▸ hWstable b hb
  have hWeq : fibre h b=W :=
    Finset.eq_of_subset_of_card_le hsub (by rw [fibre_card h b hh,hW])
  refine ⟨b,?_,?_⟩
  · rw [hWeq]
    simp [W]
  · rw [hWeq]
    exact (Finset.insert_erase hqhV).symm

theorem support_of_singleton_common (S T : Finset G) (c : G)
    (hC : S ∩ T={c}) : S=insert c (S \ T) := by
  have hc : c ∈ S ∧ c ∈ T := Finset.mem_inter.mp (by rw [hC]; simp)
  ext x
  constructor
  · intro hx
    by_cases ht : x ∈ T
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (by
        rw [← hC]; exact Finset.mem_inter.mpr ⟨hx,ht⟩)))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hx,ht⟩))
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · exact hc.1
    · exact (Finset.mem_sdiff.mp hx).1

/-- Both possible three-fibre configurations are eliminated, without assuming the catalogue. -/
theorem cyclic_four_intersection_ne_one (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsquare : ∀ z, orderedSquare S z=orderedSquare T z) :
    (S ∩ T).card ≠ 1 := by
  intro hI
  let U := S \ T
  let V := T \ S
  have hUcard : U.card=3 := by
    have he := Finset.card_sdiff_add_card_inter S T
    dsimp [U]
    omega
  have hVcard : V.card=3 := by
    have he := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at he
    dsimp [V]
    omega
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1
  have hstable : ∀ x ∈ U ∪ V, x+(m : ZMod (2*m)) ∈ U ∪ V := by
    intro x hx
    have hd : x ∈ symmDiff S T := by
      simpa only [U,V,Finset.mem_union,Finset.mem_sdiff,Finset.mem_symmDiff] using hx
    have he := (even_symmetric_difference_stable m hm S T hsquare x).mp hd
    simpa only [U,V,Finset.mem_union,Finset.mem_sdiff,Finset.mem_symmDiff] using he
  have hn : V ≠ U.image (fun x => x+(m : ZMod (2*m))) :=
    Couret.InterIA.PureExchange.cyclic_four_intersection_one_not_pure_exchange m hm S T hS hT hI hsquare
  obtain ⟨a,ha,hah⟩ := nonpure_has_pair U V m (by omega) hstable hn
  have hh := Couret.InterIA.L4.half_ne_zero m hm
  have hh2 := Couret.InterIA.L4.half_add_half m
  obtain ⟨q,hq,hUeq⟩ := split_three_with_pair U a m hh hUcard ha hah
  obtain ⟨b,hb,hVeq⟩ := complete_mixed_target U V a q m hh hh2 hVcard hdis hUeq hq hstable
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hI
  have hcST : c ∈ S ∧ c ∈ T := Finset.mem_inter.mp (by rw [hc]; simp)
  have hcU : c ∉ U := fun he => (Finset.mem_sdiff.mp he).2 hcST.2
  have hcV : c ∉ V := fun he => (Finset.mem_sdiff.mp he).2 hcST.1
  have hSe := support_of_singleton_common S T c hc
  have hTe := support_of_singleton_common T S c (by rw [Finset.inter_comm]; exact hc)
  change S=insert c U at hSe
  change T=insert c V at hTe
  have hAc : c ∉ insert q (fibre (m : ZMod (2*m)) a) := by rw [← hUeq]; exact hcU
  have hBc : c ∉ insert (q+m) (fibre (m : ZMod (2*m)) b) := by rw [← hVeq]; exact hcV
  have hSq : ∀ z, orderedSquare (insert c (insert q (fibre (m : ZMod (2*m)) a))) z=
      orderedSquare (insert c (insert (q+m) (fibre (m : ZMod (2*m)) b))) z := by
    intro z
    rw [← hUeq,← hVeq,← hSe,← hTe]
    exact hsquare z
  exact mixed_supports_cannot_collide a b c q m hh hh2 hq hAc hb hBc hSq

end Couret.InterIA.Mixed


