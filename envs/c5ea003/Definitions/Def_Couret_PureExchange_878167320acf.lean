-- Prove2me | Definitions.Def_Couret_PureExchange_878167320acf
-- name    : Couret_PureExchange_878167320acf
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:42.053706+00:00
-- url     : https://prove2.me/theorems/70b742b6-a4f2-477c-b71a-0b87964b8807
-- title:
--   Half-turn exchange lemmas
-- statement:
--   This bundle contains the finite-set reasoning for exchanging points with their antipodes under a nonzero half-turn. Its supporting lemmas track how a one-point intersection becomes a three-point intersection after the exchange and connect that operation to cyclic four-point collision constraints. It supplies proof infrastructure rather than a separate data type.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/PureExchange.lean; source file SHA-256 25558e75a03e905ae76b5810d4cdd2f4c37c61cbce110d75a1e47668a30e5b81

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
import Definitions.Def_Couret_SingleSwap_148f04e2e72b

set_option autoImplicit false
namespace Couret.InterIA.PureExchange
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem mem_translate_iff (S : Finset G) (h x : G) (hh2 : h+h=0) :
    x ∈ S.image (fun y => y+h) ↔ x+h ∈ S := by
  constructor
  · intro hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    simpa only [add_assoc,hh2,add_zero] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x+h,hx,by rw [add_assoc,hh2,add_zero]⟩

/-- Pure exchange of the changed points excludes the antipode of the unique common point. -/
theorem common_antipode_not_in_target (S T : Finset G) (h c : G)
    (hh : h ≠ 0) (hC : S ∩ T={c})
    (hexchange : T \ S=(S \ T).image (fun x => x+h)) : c+h ∉ T := by
  have hc : c ∈ S ∧ c ∈ T := Finset.mem_inter.mp (by rw [hC]; simp)
  intro hct
  by_cases hcs : c+h ∈ S
  · have he : c+h=c := Finset.mem_singleton.mp (by
      rw [← hC]; exact Finset.mem_inter.mpr ⟨hcs,hct⟩)
    exact hh (add_left_cancel (by simpa using he : c+h=c+0))
  · have hx : c+h ∈ (S \ T).image (fun x => x+h) := by
      rw [← hexchange]
      exact Finset.mem_sdiff.mpr ⟨hct,hcs⟩
    obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hx
    have hxc : x=c := add_right_cancel he
    exact (Finset.mem_sdiff.mp hx).2 (by simpa only [hxc] using hc.2)

/-- The translated target has precisely the previously noncommon source points in common. -/
theorem intersection_after_pure_exchange (S T : Finset G) (h : G)
    (hh : h ≠ 0) (hh2 : h+h=0) (hC : (S ∩ T).card=1)
    (hexchange : T \ S=(S \ T).image (fun x => x+h)) :
    S ∩ T.image (fun x => x+h)=S \ T := by
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hC
  have hcn := common_antipode_not_in_target S T h c hh hc hexchange
  ext x
  simp only [Finset.mem_inter,mem_translate_iff _ _ _ hh2,Finset.mem_sdiff]
  constructor
  · rintro ⟨hxS,hxhT⟩
    refine ⟨hxS,?_⟩
    intro hxT
    have hxc : x=c := Finset.mem_singleton.mp (by
      rw [← hc]; exact Finset.mem_inter.mpr ⟨hxS,hxT⟩)
    exact hcn (by simpa only [hxc] using hxhT)
  · rintro ⟨hxS,hxnT⟩
    have hxQ : x ∈ S \ T := Finset.mem_sdiff.mpr ⟨hxS,hxnT⟩
    have hx : x+h ∈ T \ S := by
      rw [hexchange]
      exact Finset.mem_image.mpr ⟨x,hxQ,rfl⟩
    exact ⟨hxS,(Finset.mem_sdiff.mp hx).1⟩

theorem pure_exchange_changes_one_to_three (S T : Finset G) (h : G)
    (hh : h ≠ 0) (hh2 : h+h=0) (hS : S.card=4)
    (hC : (S ∩ T).card=1)
    (hexchange : T \ S=(S \ T).image (fun x => x+h)) :
    (S ∩ T.image (fun x => x+h)).card=3 := by
  rw [intersection_after_pure_exchange S T h hh hh2 hC hexchange]
  have hc := Finset.card_sdiff_add_card_inter S T
  omega

/-- The three-Q branch of intersection one cannot have equal ordered squares. -/
theorem cyclic_four_intersection_one_not_pure_exchange (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hC : (S ∩ T).card=1)
    (hsquare : ∀ z, orderedSquare S z=orderedSquare T z) :
    T \ S ≠ (S \ T).image (fun x => x+(m : ZMod (2*m))) := by
  intro hexchange
  have hh := Couret.InterIA.L4.half_ne_zero m hm
  have hh2 := Couret.InterIA.L4.half_add_half m
  have hI := pure_exchange_changes_one_to_three S T m hh hh2 hS hC hexchange
  have hTc : (T.image (fun x => x+(m : ZMod (2*m)))).card=4 := by
    rw [Finset.card_image_of_injective _ (fun x y he => add_right_cancel he),hT]
  have hEq : ∀ z, orderedSquare S z=
      orderedSquare (T.image (fun x => x+(m : ZMod (2*m)))) z := by
    intro z
    rw [Couret.InterIA.Translation.two_torsion_translation_preserves_square T m hh2 z]
    exact hsquare z
  exact Couret.InterIA.IntersectionThree.cyclic_four_intersection_ne_three m hm S
    (T.image (fun x => x+(m : ZMod (2*m)))) hS hTc hEq hI

end Couret.InterIA.PureExchange


