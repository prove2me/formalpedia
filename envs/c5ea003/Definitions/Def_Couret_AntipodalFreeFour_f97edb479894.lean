-- Prove2me | Definitions.Def_Couret_AntipodalFreeFour_f97edb479894
-- name    : Couret_AntipodalFreeFour_f97edb479894
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:05:45.85096+00:00
-- url     : https://prove2.me/theorems/d29ace5d-f13c-4bed-9724-87ebe43c88f4
-- title:
--   Antipodal-free cyclic four-supports
-- statement:
--   For $S\subseteq\mathbb Z/(2m)\mathbb Z$, antipodal freeness means
--
--   $$x\in S\Longrightarrow x+m\notin S.$$
--
--   The bundle also supplies the collision and fibre descriptions for antipodal-free four-element supports when $m>0$: any four-support with the same ordered-square counts is $S$ or its half translate $S+m$. This provides the antipodal-free branch of cyclic fibre classification.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/AntipodalFreeFour.lean; source file SHA-256 7d4d6262bdcf95ddc7a9a560bac4324cde190e4dad3f7acc41bcda6a4ccb23ed

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_DisjointReduction_b47db5028f89

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

/-- Every occupied antipodal pair of S is simple. -/
def AntipodalFree (m : ℕ) (S : Finset (ZMod (2*m))) : Prop :=
  ∀ x ∈ S, x+(m : ZMod (2*m)) ∉ S

/-- Original Finset and natural orderedSquare API, including diagonals and all affine cases. -/
theorem antipodal_free_four_collision (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hfree : AntipodalFree m S)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    T=S ∨ T=S.image (fun x => x+(m : ZMod (2*m))) := by
  rcases Couret.InterIA.NormalForm.cyclic_intersection_card_cases m hm S T hS hT hsq
    with h0|h2|h4
  · right
    have hd := Couret.InterIA.NormalForm.disjoint_of_inter_zero S T h0
    have hsub : S.image (fun x => x+(m : ZMod (2*m))) ⊆ T := by
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hnt : x ∉ T := fun ht => Finset.disjoint_left.mp hd hx ht
      have hst : x ∈ symmDiff S T := Finset.mem_symmDiff.mpr (Or.inl ⟨hx,hnt⟩)
      have hh := (even_symmetric_difference_stable m hm S T hsq x).mp hst
      rcases Finset.mem_symmDiff.mp hh with hh|hh
      · exact False.elim (hfree x hx hh.1)
      · exact hh.1
    have hcard : (S.image (fun x => x+(m : ZMod (2*m)))).card = S.card :=
      Finset.card_image_of_injective S (fun _ _ he => add_right_cancel he)
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard,hS,hT])).symm
  · rcases Couret.InterIA.IntersectionTwo.cyclic_four_intersection_two_dichotomy
      m hm S T hS hT h2 hsq with hpp|hh
    · obtain ⟨a,b,hSa,_⟩ := hpp
      have ha : a ∈ S \ T := by rw [hSa]; simp [fibre]
      have hah : a+(m : ZMod (2*m)) ∈ S \ T := by rw [hSa]; simp [fibre]
      exact False.elim (hfree a (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hah).1)
    · exact Or.inr hh.symm
  · exact Or.inl (Couret.InterIA.NormalForm.eq_of_full_intersection S T hS hT h4).symm



/-- The entire original four-point fibre is precisely this pair of distinct supports. -/
theorem antipodal_free_four_fibre_eq_pair (m : ℕ) (hm : 0 < m)
    (S : Finset (ZMod (2*m))) (hS : S.card=4) (hfree : AntipodalFree m S) :
    {T : Finset (ZMod (2*m)) | T.card=4 ∧ ∀ z, orderedSquare S z=orderedSquare T z} =
      {S,S.image (fun x => x+(m : ZMod (2*m)))} := by
  ext T
  simp only [Set.mem_setOf_eq,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨hT,hsq⟩
    exact antipodal_free_four_collision m hm S T hS hT hfree hsq
  · rintro (rfl|rfl)
    · exact ⟨hS,fun _ => rfl⟩
    · constructor
      · have he : (S.image (fun x => x+(m : ZMod (2*m)))).card=S.card :=
          Finset.card_image_of_injective S (fun _ _ he => add_right_cancel he)
        simpa only [he] using hS
      · intro z
        exact (Couret.InterIA.Translation.two_torsion_translation_preserves_square S
          (m : ZMod (2*m)) (Couret.InterIA.L4.half_add_half m) z).symm

end Couret.InterIA.Fibres


