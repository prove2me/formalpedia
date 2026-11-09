-- Prove2me | Definitions.Def_Couret_IntersectionTwo_2d7b2419466c
-- name    : Couret_IntersectionTwo_2d7b2419466c
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:02:05.671943+00:00
-- url     : https://prove2.me/theorems/22e91152-e280-4778-afc8-3b8c61fc7963
-- title:
--   Geometry of four-support collisions with overlap two
-- statement:
--   This bundle supplies the structural API for two four-element supports sharing two points and equal ordered-square data in a group whose doubling kernel is $\{0,h\}$ for a nonzero involution $h$. The resulting dichotomy is that their exclusive two-point parts are antipodal pairs, or the full supports are translates by $h$.
--
--   Supporting results handle half-turn-stable unions, complements and pairs, and the cyclic specialization in $\mathbb Z/(2m)\mathbb Z$ with $m>0$. These lemmas make the overlap-two branch reusable by the fibre constructions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/IntersectionTwo.lean; source file SHA-256 e2c77e9e622dffdbb4d1ff0106496bedf3d7a473e3aa12fb34654a7500cbc465

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
import Definitions.Def_Couret_IntersectionTwoAlgebra_ba9c300e13f5

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem stable_union_complement (U V : Finset G) (h : G) (hh2 : h+h=0)
    (hd : Disjoint U V) (hU : ∀ x ∈ U, x+h ∈ U)
    (hUV : ∀ x ∈ U ∪ V, x+h ∈ U ∪ V) : ∀ x ∈ V, x+h ∈ V := by
  intro x hx
  rcases Finset.mem_union.mp (hUV x (Finset.mem_union_right U hx)) with hp|hp
  · have hback := hU (x+h) hp
    rw [add_assoc,hh2,add_zero] at hback
    exact False.elim (Finset.disjoint_left.mp hd hback hx)
  · exact hp

/-- Equal-sized differences with two elements give only P/P or Q/Q.
This step needs an involution, not a cyclic doubling kernel. -/
theorem two_pair_fibre_dichotomy (U V : Finset G) (h : G) (hh : h ≠ 0)
    (hh2 : h+h=0) (hU : U.card=2) (hV : V.card=2) (hd : Disjoint U V)
    (hst : ∀ x ∈ U ∪ V, x+h ∈ U ∪ V) :
    (∃ a b, U=fibre h a ∧ V=fibre h b) ∨
    (∃ a b, a ≠ b ∧ b ≠ a+h ∧ U=({a,b} : Finset G) ∧
      V=({a+h,b+h} : Finset G)) := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hU
  have hshift : ∀ x : G, x+h ≠ x := by
    intro x he
    exact hh (add_left_cancel (by simpa using he : x+h=x+0))
  by_cases hba : b=a+h
  · left
    have hUp : ∀ x ∈ ({a,b} : Finset G), x+h ∈ ({a,b} : Finset G) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with hx|hx
      · rw [hx]; simp [hba]
      · rw [hx]
        have hb : b+h=a := by rw [hba,add_assoc,hh2,add_zero]
        simp [hb]
    have hVp := stable_union_complement {a,b} V h hh2 hd hUp hst
    obtain ⟨c,d,hcd,hVeq⟩ := Finset.card_eq_two.mp hV
    have hch := hVp c (by rw [hVeq]; simp)
    rw [hVeq] at hch
    have hdc : d=c+h := by
      simp only [mem_insert,mem_singleton] at hch
      exact (hch.resolve_left (hshift c)).symm
    exact ⟨a,c,by simp [fibre,hba],by simp [hVeq,fibre,hdc]⟩
  · right
    have hah : a+h ∉ ({a,b} : Finset G) := by
      simp only [mem_insert,mem_singleton,not_or]
      exact ⟨hshift a,Ne.symm hba⟩
    have hbh : b+h ∉ ({a,b} : Finset G) := by
      simp only [mem_insert,mem_singleton,not_or]
      refine ⟨?_,hshift b⟩
      intro he
      apply hba
      calc b=(b+h)+h := by rw [add_assoc,hh2,add_zero]
           _=a+h := by rw [he]
    have haV : a+h ∈ V :=
      (Finset.mem_union.mp (hst a (by simp))).resolve_left hah
    have hbV : b+h ∈ V :=
      (Finset.mem_union.mp (hst b (by simp))).resolve_left hbh
    have hp : ({a+h,b+h} : Finset G) ⊆ V := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl <;> assumption
    have hcard : ({a+h,b+h} : Finset G).card=2 := by
      apply Finset.card_pair
      exact fun he => hab (add_right_cancel he)
    have he := Finset.eq_of_subset_of_card_le hp (by omega)
    exact ⟨a,b,hab,hba,rfl,he.symm⟩

theorem stable_pair_of_antipodal (c h : G) (hh2 : h+h=0) :
    ∀ z ∈ ({c,c+h} : Finset G), z+h ∈ ({c,c+h} : Finset G) := by
  intro z hz
  simp only [mem_insert,mem_singleton] at hz
  rcases hz with rfl|rfl
  · simp
  · simp [add_assoc,hh2]

theorem image_eq_self_of_stable (C : Finset G) (h : G) (hh2 : h+h=0)
    (hc : ∀ z ∈ C, z+h ∈ C) : C.image (fun x => x+h)=C := by
  ext z
  constructor
  · intro hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact hc x hx
  · intro hz
    exact Finset.mem_image.mpr ⟨z+h,hc z hz,by rw [add_assoc,hh2,add_zero]⟩

/-- QQ is completely classified under the stated doubling kernel hypothesis. -/
theorem qq_collision_is_half_translation (C : Finset G) (h : G)
    (hh : h ≠ 0) (hh2 : h+h=0)
    (hkernel : ∀ x : G, x+x=0 → x=0 ∨ x=h)
    (a b : G) (hab : a ≠ b) (hbah : b ≠ a+h) (hC : C.card=2)
    (hCU : Disjoint C ({a,b} : Finset G))
    (hCV : Disjoint C (({a,b} : Finset G).image (fun x => x+h)))
    (hsq : ∀ z, orderedSquare (C ∪ {a,b}) z =
      orderedSquare (C ∪ ({a,b} : Finset G).image (fun x => x+h)) z) :
    C.image (fun x => x+h)=C ∧
    (C ∪ {a,b}).image (fun x => x+h)=
      C ∪ ({a,b} : Finset G).image (fun x => x+h) := by
  have he := translated_difference_cross C {a,b} h hh2 hCU hCV hsq
  obtain ⟨c,d,hcd,hCeq⟩ := Finset.card_eq_two.mp hC
  have hdc := qq_common_antipodal h hh hh2 hkernel a b c d hab hbah hcd
    (by simpa only [hCeq] using he)
  have hstable : C.image (fun x => x+h)=C := by
    rw [hCeq,hdc]
    exact image_eq_self_of_stable {c,c+h} h hh2 (stable_pair_of_antipodal c h hh2)
  exact ⟨hstable,by rw [Finset.image_union,hstable]⟩

/-- Intrinsic intersection-two conclusion, conditional only on the involution
and its exact doubling kernel. Other intersection sizes are not asserted. -/
theorem four_intersection_two_dichotomy (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (hkernel : ∀ x : G, x+x=0 → x=0 ∨ x=h)
    (S T : Finset G) (hS : S.card=4) (hT : T.card=4) (hI : (S ∩ T).card=2)
    (hst : ∀ x ∈ symmDiff S T, x+h ∈ symmDiff S T)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    (∃ a b, S \ T=fibre h a ∧ T \ S=fibre h b) ∨
      S.image (fun x => x+h)=T := by
  have hcS := Finset.card_sdiff_add_card_inter S T
  have hcT := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at hcT
  have hD : symmDiff S T=(S \ T) ∪ (T \ S) := by
    ext x
    simp only [mem_symmDiff,mem_union,mem_sdiff]
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1
  have hst' : ∀ x ∈ (S \ T) ∪ (T \ S), x+h ∈ (S \ T) ∪ (T \ S) := by
    simpa only [← hD] using hst
  rcases two_pair_fibre_dichotomy (S \ T) (T \ S) h hh hh2
    (by omega) (by omega) hd hst' with hpp|hqq
  · exact Or.inl hpp
  · right
    obtain ⟨a,b,hab,hbah,hU,hV⟩ := hqq
    have heS : S=(S ∩ T) ∪ {a,b} := by
      rw [← hU]
      ext x
      simp only [mem_union,mem_inter,mem_sdiff]
      tauto
    have heT : T=(S ∩ T) ∪ ({a,b} : Finset G).image (fun x => x+h) := by
      have himg : ({a,b} : Finset G).image (fun x => x+h)={a+h,b+h} := by simp
      rw [himg,← hV]
      ext x
      simp only [mem_union,mem_inter,mem_sdiff]
      tauto
    have hdU : Disjoint (S ∩ T) ({a,b} : Finset G) := by
      rw [← hU]
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (mem_sdiff.mp hy).2 (mem_inter.mp hx).2
    have hdV : Disjoint (S ∩ T) (({a,b} : Finset G).image (fun x => x+h)) := by
      have himg : ({a,b} : Finset G).image (fun x => x+h)={a+h,b+h} := by simp
      rw [himg,← hV]
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (mem_sdiff.mp hy).2 (mem_inter.mp hx).1
    have he := qq_collision_is_half_translation (S ∩ T) h hh hh2 hkernel a b hab hbah hI hdU hdV
      (by simpa only [← heS,← heT] using hsq)
    simpa only [← heS,← heT] using he.2

theorem cyclic_four_intersection_two_dichotomy (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hI : (S ∩ T).card=2) (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    (∃ a b, S \ T=fibre (m : ZMod (2*m)) a ∧ T \ S=fibre (m : ZMod (2*m)) b) ∨
      S.image (fun x => x+(m : ZMod (2*m)))=T := by
  exact four_intersection_two_dichotomy (m : ZMod (2*m))
    (Couret.InterIA.L4.half_ne_zero m hm) (Couret.InterIA.L4.half_add_half m)
    (Couret.InterIA.L4.doubling_kernel m hm) S T hS hT hI
    (fun x hx => (even_symmetric_difference_stable m hm S T hsq x).mp hx) hsq









end Couret.InterIA.IntersectionTwo


