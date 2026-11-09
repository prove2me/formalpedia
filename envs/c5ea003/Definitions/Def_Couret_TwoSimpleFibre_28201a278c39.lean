-- Prove2me | Definitions.Def_Couret_TwoSimpleFibre_28201a278c39
-- name    : Couret_TwoSimpleFibre_28201a278c39
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:09:22.658431+00:00
-- url     : https://prove2.me/theorems/e3795faa-3297-45bf-abd6-330b20db718a
-- title:
--   Four-point fibres with one full antipodal pair
-- statement:
--   The half-shift translates by $m$ in $\mathbb Z/(2m)$. The original fibre records four-point supports with the same ordered square. Admissible full antipodal pairs and an orientation code describe supports obtained by combining a two-point remainder with one full pair. A noncomputable equivalence packages the resulting fibre description, supplying its size and binary orientation structure.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoSimpleFibre.lean; source file SHA-256 06c3e6b8dbdb8d80fbe47dc48b06485708ba310ea7e7b7b8681b9c42b32966b7

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_WeightedFullPosition_056084203332
import Definitions.Def_Couret_AntipodalFreeFour_f97edb479894
import Definitions.Def_Couret_QuotientBridge_26f10959e8eb
import Mathlib.Data.Set.Card

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.NormalForm
open Couret.InterIA.Projection Couret.InterIA.GroupRing Couret.InterIA.IntersectionTwo

def halfShift (m : ℕ) (S : Finset (ZMod (2*m))) : Finset (ZMod (2*m)) :=
  S.image (fun x => x+(m : ZMod (2*m)))

theorem halfShift_twice (m : ℕ) (S : Finset (ZMod (2*m))) :
    halfShift m (halfShift m S)=S :=
  shift_twice S m (Couret.InterIA.L4.half_add_half m)

theorem halfShift_fibre (m : ℕ) (a : ZMod (2*m)) :
    halfShift m (fibre (m : ZMod (2*m)) a)=fibre (m : ZMod (2*m)) a := by
  have hh := Couret.InterIA.L4.half_add_half m
  simp [halfShift,fibre,add_assoc,hh,Finset.pair_comm]

theorem halfShift_union_fibre (m : ℕ) (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) :
    halfShift m (C ∪ fibre (m : ZMod (2*m)) a)=halfShift m C ∪ fibre (m : ZMod (2*m)) a := by
  change (C ∪ fibre (m : ZMod (2*m)) a).image _ = _
  rw [Finset.image_union]
  exact congrArg (fun D => halfShift m C ∪ D) (halfShift_fibre m a)

theorem presentation_single_point (m : ℕ) (C : Finset (ZMod (2*m)))
    (a : ZMod (2*m)) (hfree : AntipodalFree m C) (hd : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    ∀ x ∈ C, x+(m : ZMod (2*m)) ∉ C ∪ fibre (m : ZMod (2*m)) a := by
  intro x hx hmem
  rcases Finset.mem_union.mp hmem with hc|hf
  · exact hfree x hx hc
  · have hback := stable_pair_of_antipodal a (m : ZMod (2*m))
      (Couret.InterIA.L4.half_add_half m) (x+m) hf
    have hxf : x ∈ fibre (m : ZMod (2*m)) a := by
      simpa only [add_assoc,Couret.InterIA.L4.half_add_half,add_zero,fibre] using hback
    exact Finset.disjoint_left.mp hd hx hxf

theorem presentation_unique_full_pair (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a b : ZMod (2*m))
    (hfree : AntipodalFree m C) (hd : Disjoint C (fibre (m : ZMod (2*m)) a))
    (hb : fibre (m : ZMod (2*m)) b ⊆ C ∪ fibre (m : ZMod (2*m)) a) : fibre (m : ZMod (2*m)) b=fibre (m : ZMod (2*m)) a := by
  have hsingle := presentation_single_point m C a hfree hd
  have hsub : fibre (m : ZMod (2*m)) b ⊆ fibre (m : ZMod (2*m)) a := by
    intro x hx
    rcases Finset.mem_union.mp (hb hx) with hc|ha
    · have hmate := stable_pair_of_antipodal b (m : ZMod (2*m))
        (Couret.InterIA.L4.half_add_half m) x hx
      exact False.elim (hsingle x hc (hb hmate))
    · exact ha
  exact Finset.eq_of_subset_of_card_le hsub
    (by rw [fibre_card (m : ZMod (2*m)) a (Couret.InterIA.L4.half_ne_zero m hm),
      fibre_card (m : ZMod (2*m)) b (Couret.InterIA.L4.half_ne_zero m hm)])

theorem presentation_normal_peel (m : ℕ) (hm : 0 < m)
    (C T : Finset (ZMod (2*m))) (a : ZMod (2*m))
    (hfree : AntipodalFree m C) (hd : Disjoint C (fibre (m : ZMod (2*m)) a))
    (hn : Normal (m : ZMod (2*m)) (C ∪ fibre (m : ZMod (2*m)) a) T) :
    ∃ b : ZMod (2*m), Disjoint C (fibre (m : ZMod (2*m)) b) ∧ T=C ∪ fibre (m : ZMod (2*m)) b := by
  obtain ⟨u,b,hu,hb⟩ := hn.2
  have hsub : fibre (m : ZMod (2*m)) u ⊆ C ∪ fibre (m : ZMod (2*m)) a := by
    rw [← hu]
    exact Finset.sdiff_subset
  have hfull := presentation_unique_full_pair m hm C a u hfree hd hsub
  rw [hfull] at hu
  have hCT : C ⊆ T := by
    intro x hx
    by_contra hnt
    have hh : x ∈ (C ∪ fibre (m : ZMod (2*m)) a) \ T := Finset.mem_sdiff.mpr
      ⟨Finset.mem_union.mpr (Or.inl hx),hnt⟩
    rw [hu] at hh
    exact Finset.disjoint_left.mp hd hx hh
  have hcommon : (C ∪ fibre (m : ZMod (2*m)) a) ∩ T=C := by
    ext x
    constructor
    · intro hx
      obtain ⟨hS,hT⟩ := Finset.mem_inter.mp hx
      rcases Finset.mem_union.mp hS with hc|hf
      · exact hc
      · rw [← hu] at hf
        exact False.elim ((Finset.mem_sdiff.mp hf).2 hT)
    · intro hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl hx),hCT hx⟩
  refine ⟨b,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hf
    rw [← hb] at hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_union.mpr (Or.inl hx))
  · rw [← hcommon,← hb]
    ext x
    simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff]
    tauto

/-- No non-affine assumption: a non-stable support has only these four structural cases. -/
theorem nonstable_four_collision_cases (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hnst : ¬ ∀ x ∈ S, x+(m : ZMod (2*m)) ∈ S)
    (hsq : ∀ z, orderedSquare S z=orderedSquare T z) :
    T=S ∨ T=halfShift m S ∨ Normal (m : ZMod (2*m)) S T ∨
      Normal (m : ZMod (2*m)) S (halfShift m T) := by
  rcases cyclic_intersection_card_cases m hm S T hS hT hsq with h0|h2|h4
  · have hd := disjoint_of_inter_zero S T h0
    have hU : (halfShift m T).card=4 := by
      unfold halfShift
      rw [Finset.card_image_of_injective _ (fun _ _ he => add_right_cancel he),hT]
    have hsU : ∀ z, orderedSquare S z=orderedSquare (halfShift m T) z := by
      intro z
      unfold halfShift
      rw [Couret.InterIA.Translation.two_torsion_translation_preserves_square T m
        (Couret.InterIA.L4.half_add_half m)]
      exact hsq z
    rcases cyclic_intersection_card_cases m hm S (halfShift m T) hS hU hsU with hU0|hU2|hU4
    · have hdU := disjoint_of_inter_zero S (halfShift m T) hU0
      have hstable : ∀ x ∈ S ∪ T, x+(m : ZMod (2*m)) ∈ S ∪ T := by
        intro x hx
        have hdiff : symmDiff S T=S ∪ T := by
          ext y
          simp only [Finset.mem_symmDiff,Finset.mem_union]
          have hn : ¬ (y ∈ S ∧ y ∈ T) := fun h => Finset.disjoint_left.mp hd h.1 h.2
          tauto
        rw [← hdiff] at hx ⊢
        exact (even_symmetric_difference_stable m hm S T hsq x).mp hx
      exact False.elim (hnst (doubly_disjoint_stable S T m
        (Couret.InterIA.L4.half_add_half m) hd hdU hstable).1)
    · rcases cyclic_four_intersection_two_dichotomy m hm S (halfShift m T) hS hU hU2 hsU with hp|hh
      · exact Or.inr (Or.inr (Or.inr ⟨hU2,hp⟩))
      · have he := congrArg (halfShift m) hh
        change halfShift m (halfShift m S)=halfShift m (halfShift m T) at he
        rw [halfShift_twice,halfShift_twice] at he
        exact Or.inl he.symm
    · have he := eq_of_full_intersection S (halfShift m T) hS hU hU4
      have hh := congrArg (halfShift m) he
      rw [halfShift_twice] at hh
      exact Or.inr (Or.inl hh.symm)
  · rcases cyclic_four_intersection_two_dichotomy m hm S T hS hT h2 hsq with hp|hh
    · exact Or.inr (Or.inr (Or.inl ⟨h2,hp⟩))
    · exact Or.inr (Or.inl hh.symm)
  · exact Or.inl (eq_of_full_intersection S T hS hT h4).symm

theorem two_simple_collision_representation (m : ℕ) (hm : 0 < m)
    (C T : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (hd : Disjoint C (fibre (m : ZMod (2*m)) a))
    (hT : T.card=4)
    (hsq : ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z=orderedSquare T z) :
    ∃ b : ZMod (2*m), Disjoint C (fibre (m : ZMod (2*m)) b) ∧
      (T=C ∪ fibre (m : ZMod (2*m)) b ∨ T=halfShift m C ∪ fibre (m : ZMod (2*m)) b) := by
  have hS : (C ∪ fibre (m : ZMod (2*m)) a).card=4 := by
    rw [Finset.card_union_of_disjoint hd,hC,
      fibre_card (m : ZMod (2*m)) a (Couret.InterIA.L4.half_ne_zero m hm)]
  have hn : ¬ ∀ x ∈ C ∪ fibre (m : ZMod (2*m)) a, x+(m : ZMod (2*m)) ∈ C ∪ fibre (m : ZMod (2*m)) a := by
    intro hst
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
    exact presentation_single_point m C a hfree hd x hx
      (hst x (Finset.mem_union.mpr (Or.inl hx)))
  rcases nonstable_four_collision_cases m hm (C ∪ fibre (m : ZMod (2*m)) a) T hS hT hn hsq with h|h|h|h
  · exact ⟨a,hd,Or.inl h⟩
  · exact ⟨a,hd,Or.inr (h.trans (halfShift_union_fibre m C a))⟩
  · obtain ⟨b,hb,ht⟩ := presentation_normal_peel m hm C T a hfree hd h
    exact ⟨b,hb,Or.inl ht⟩
  · obtain ⟨b,hb,ht⟩ := presentation_normal_peel m hm C (halfShift m T) a hfree hd h
    have hh := congrArg (halfShift m) ht
    rw [halfShift_twice,halfShift_union_fibre] at hh
    exact ⟨b,hb,Or.inr hh⟩

theorem disjoint_full_pair_projection_ne (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a x : ZMod (2*m))
    (hd : Disjoint C (fibre (m : ZMod (2*m)) a)) (hx : x ∈ C) :
    projection m x ≠ projection m a := by
  intro he
  have hf : x ∈ fibre (m : ZMod (2*m)) a := by
    rcases (projection_eq_iff m hm a x).mp he.symm with rfl|rfl <;> simp [fibre]
  exact Finset.disjoint_left.mp hd hx hf

theorem fibre_eq_of_projection_eq (m : ℕ) (hm : 0 < m) (a b : ZMod (2*m))
    (he : projection m a=projection m b) : fibre (m : ZMod (2*m)) a=fibre (m : ZMod (2*m)) b := by
  by_contra hn
  exact projection_distinct m hm a b hn he

theorem presentation_weighted_push (m : ℕ) (hm : 0 < m)
    (i j a : ZMod (2*m)) (hij : i ≠ j)
    (hd : Disjoint ({i,j} : Finset (ZMod (2*m))) (fibre (m : ZMod (2*m)) a)) :
    push m (indicator ({i,j} ∪ fibre (m : ZMod (2*m)) a))=
      weightedProfile (projection m i) (projection m j) (projection m a) := by
  rw [indicator_union_disjoint _ _ hd,map_add,push_fibre m hm a,
    indicator_pair i j hij,map_add,Couret.InterIA.QuotientBridge.push_atom,
    Couret.InterIA.QuotientBridge.push_atom]
  rfl

theorem presentation_weighted_square (m : ℕ) (hm : 0 < m)
    (i j a b : ZMod (2*m)) (hij : i ≠ j)
    (ha : Disjoint ({i,j} : Finset (ZMod (2*m))) (fibre (m : ZMod (2*m)) a))
    (hb : Disjoint ({i,j} : Finset (ZMod (2*m))) (fibre (m : ZMod (2*m)) b))
    (hsq : ∀ z, orderedSquare ({i,j} ∪ fibre (m : ZMod (2*m)) a) z=
      orderedSquare ({i,j} ∪ fibre (m : ZMod (2*m)) b) z) :
    weightedProfile (projection m i) (projection m j) (projection m a)^2=
      weightedProfile (projection m i) (projection m j) (projection m b)^2 := by
  have he := congrArg (push m) ((square_equality_iff _ _).mpr hsq)
  rw [map_mul,map_mul,presentation_weighted_push m hm i j a hij ha,
    presentation_weighted_push m hm i j b hij hb] at he
  simpa only [pow_two] using he

/-- At most one different admissible full pair in the actual convolution problem. -/
theorem presentation_full_pair_unique (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (hC : C.card=2) (a b d : ZMod (2*m))
    (ha : Disjoint C (fibre (m : ZMod (2*m)) a))
    (hb : Disjoint C (fibre (m : ZMod (2*m)) b))
    (hd : Disjoint C (fibre (m : ZMod (2*m)) d))
    (hba : fibre (m : ZMod (2*m)) b ≠ fibre (m : ZMod (2*m)) a)
    (hda : fibre (m : ZMod (2*m)) d ≠ fibre (m : ZMod (2*m)) a)
    (hsb : ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z=orderedSquare (C ∪ fibre (m : ZMod (2*m)) b) z)
    (hsd : ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z=orderedSquare (C ∪ fibre (m : ZMod (2*m)) d) z) :
    fibre (m : ZMod (2*m)) b=fibre (m : ZMod (2*m)) d := by
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hC
  have hqi : i ∈ ({i,j} : Finset (ZMod (2*m))) := by simp
  have hqb : projection m b ≠ projection m a := fun he => hba (fibre_eq_of_projection_eq m hm b a he)
  have hqd : projection m d ≠ projection m a := fun he => hda (fibre_eq_of_projection_eq m hm d a he)
  apply fibre_eq_of_projection_eq m hm b d
  exact weighted_full_position_unique (projection m i) (projection m j)
    (projection m a) (projection m b) (projection m d) hqb hqd
    (disjoint_full_pair_projection_ne m hm {i,j} a i ha hqi)
    (disjoint_full_pair_projection_ne m hm {i,j} b i hb hqi)
    (disjoint_full_pair_projection_ne m hm {i,j} d i hd hqi)
    (presentation_weighted_square m hm i j a b hij ha hb hsb)
    (presentation_weighted_square m hm i j a d hij ha hd hsd)

def originalFibre (m : ℕ) (S : Finset (ZMod (2*m))) : Set (Finset (ZMod (2*m))) :=
  {T | T.card=4 ∧ ∀ z, orderedSquare S z=orderedSquare T z}

def admissibleFullPairs (m : ℕ) (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) :
    Set (Finset (ZMod (2*m))) :=
  {D | ∃ b : ZMod (2*m), D=fibre (m : ZMod (2*m)) b ∧ Disjoint C D ∧
    ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z=orderedSquare (C ∪ D) z}

theorem admissible_full_pair_base (m : ℕ) (C : Finset (ZMod (2*m))) (a : ZMod (2*m))
    (hd : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    fibre (m : ZMod (2*m)) a ∈ admissibleFullPairs m C a :=
  ⟨a,rfl,hd,fun _ => rfl⟩

theorem admissible_full_pairs_unique (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (hC : C.card=2) (a : ZMod (2*m))
    (ha : Disjoint C (fibre (m : ZMod (2*m)) a))
    (D E : Finset (ZMod (2*m))) (hD : D ∈ admissibleFullPairs m C a)
    (hE : E ∈ admissibleFullPairs m C a)
    (hDa : D ≠ fibre (m : ZMod (2*m)) a) (hEa : E ≠ fibre (m : ZMod (2*m)) a) : D=E := by
  obtain ⟨b,rfl,hb,hsb⟩ := hD
  obtain ⟨d,rfl,hd,hsd⟩ := hE
  exact presentation_full_pair_unique m hm C hC a b d ha hb hd hDa hEa hsb hsd

/-- The admissible full-pair family is exactly a singleton or a pair. -/
theorem admissible_full_pairs_one_or_two (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (hC : C.card=2) (a : ZMod (2*m))
    (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    admissibleFullPairs m C a={fibre (m : ZMod (2*m)) a} ∨
    ∃ D : Finset (ZMod (2*m)), D ≠ fibre (m : ZMod (2*m)) a ∧
      admissibleFullPairs m C a={fibre (m : ZMod (2*m)) a,D} := by
  classical
  have hbase := admissible_full_pair_base m C a ha
  by_cases hall : ∀ D ∈ admissibleFullPairs m C a, D=fibre (m : ZMod (2*m)) a
  · left
    ext D
    constructor
    · intro hD; exact Set.mem_singleton_iff.mpr (hall D hD)
    · intro hD; rw [Set.mem_singleton_iff.mp hD]; exact hbase
  · push Not at hall
    obtain ⟨D,hD,hDa⟩ := hall
    refine Or.inr ⟨D,hDa,?_⟩
    ext E
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hE
      by_cases hEa : E=fibre (m : ZMod (2*m)) a
      · exact Or.inl hEa
      · exact Or.inr (admissible_full_pairs_unique m hm C hC a ha E D hE hD hEa hDa)
    · rintro (rfl|rfl)
      · exact hbase
      · exact hD

/-- The entire actual fibre is the product of the two orientations and the full-pair family. -/
theorem two_simple_fibre_rectangle (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    originalFibre m (C ∪ fibre (m : ZMod (2*m)) a) =
      (fun D => C ∪ D) '' admissibleFullPairs m C a ∪
      (fun D => halfShift m C ∪ D) '' admissibleFullPairs m C a := by
  ext T
  constructor
  · rintro ⟨hT,hsq⟩
    obtain ⟨b,hb,ht⟩ := two_simple_collision_representation m hm C T a hC hfree ha hT hsq
    rcases ht with ht|ht
    · left
      refine ⟨fibre (m : ZMod (2*m)) b,⟨b,rfl,hb,?_⟩,ht.symm⟩
      simpa only [← ht] using hsq
    · right
      refine ⟨fibre (m : ZMod (2*m)) b,⟨b,rfl,hb,?_⟩,ht.symm⟩
      have hsqH : ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z=
          orderedSquare (halfShift m T) z := by
        intro z
        unfold halfShift
        rw [Couret.InterIA.Translation.two_torsion_translation_preserves_square T m
          (Couret.InterIA.L4.half_add_half m)]
        exact hsq z
      have hh : halfShift m T=C ∪ fibre (m : ZMod (2*m)) b := by
        rw [ht,halfShift_union_fibre,halfShift_twice]
      simpa only [hh] using hsqH
  · rintro (⟨D,hD,rfl⟩|⟨D,hD,rfl⟩)
    · obtain ⟨b,rfl,hb,hsb⟩ := hD
      refine ⟨?_,hsb⟩
      rw [Finset.card_union_of_disjoint hb,hC,
        fibre_card (m : ZMod (2*m)) b (Couret.InterIA.L4.half_ne_zero m hm)]
    · obtain ⟨b,rfl,hb,hsb⟩ := hD
      have hcard : (C ∪ fibre (m : ZMod (2*m)) b).card=4 := by
        rw [Finset.card_union_of_disjoint hb,hC,
          fibre_card (m : ZMod (2*m)) b (Couret.InterIA.L4.half_ne_zero m hm)]
      have hh : halfShift m C ∪ fibre (m : ZMod (2*m)) b =
          halfShift m (C ∪ fibre (m : ZMod (2*m)) b) := (halfShift_union_fibre m C b).symm
      dsimp only
      rw [hh]
      constructor
      · unfold halfShift
        rw [Finset.card_image_of_injective _ (fun _ _ he => add_right_cancel he)]
        exact hcard
      · intro z
        unfold halfShift
        rw [Couret.InterIA.Translation.two_torsion_translation_preserves_square _ (m : ZMod (2*m))
          (Couret.InterIA.L4.half_add_half m)]
        exact hsb z

theorem admissible_union_injective (m : ℕ) (C : Finset (ZMod (2*m))) (a : ZMod (2*m))
    (D E : Finset (ZMod (2*m))) (hD : D ∈ admissibleFullPairs m C a)
    (hE : E ∈ admissibleFullPairs m C a) (heq : C ∪ D=C ∪ E) : D=E := by
  obtain ⟨b,hDb,hd,_⟩ := hD
  obtain ⟨d,hEd,he,_⟩ := hE
  ext x
  by_cases hx : x ∈ C
  · have hnD : x ∉ D := fun h => Finset.disjoint_left.mp hd hx h
    have hnE : x ∉ E := fun h => Finset.disjoint_left.mp he hx h
    simp [hnD,hnE]
  · have hh : (x ∈ C ∪ D) ↔ (x ∈ C ∪ E) := by rw [heq]
    simpa only [Finset.mem_union,hx,false_or] using hh

theorem admissible_orientation_distinct (m : ℕ) (C : Finset (ZMod (2*m)))
    (a : ZMod (2*m)) (hC : C.card=2) (hfree : AntipodalFree m C)
    (D E : Finset (ZMod (2*m))) (_hD : D ∈ admissibleFullPairs m C a)
    (hE : E ∈ admissibleFullPairs m C a) : C ∪ D ≠ halfShift m C ∪ E := by
  intro heq
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < C.card by omega)
  have hleft : x ∈ C ∪ D := Finset.mem_union.mpr (Or.inl hx)
  rw [heq] at hleft
  rcases Finset.mem_union.mp hleft with hh|he
  · obtain ⟨y,hy,hye⟩ := Finset.mem_image.mp hh
    apply hfree y hy
    simpa only [hye] using hx
  · obtain ⟨b,hEb,hdisj,_⟩ := hE
    exact Finset.disjoint_left.mp hdisj hx he

theorem halfShift_union (m : ℕ) (C D : Finset (ZMod (2*m))) :
    halfShift m (C ∪ D)=halfShift m C ∪ halfShift m D := by
  unfold halfShift
  rw [Finset.image_union]

def orientationCode (m : ℕ) (C : Finset (ZMod (2*m))) (a : ZMod (2*m))
    (p : Bool × {D : Finset (ZMod (2*m)) // D ∈ admissibleFullPairs m C a}) :
    Finset (ZMod (2*m)) := if p.1 then halfShift m C ∪ p.2.1 else C ∪ p.2.1

/-- No two orientation/full-pair codes describe the same support. -/
theorem orientationCode_injective (m : ℕ) (C : Finset (ZMod (2*m)))
    (a : ZMod (2*m)) (hC : C.card=2) (hfree : AntipodalFree m C) :
    Function.Injective (orientationCode m C a) := by
  rintro ⟨e,D⟩ ⟨f,E⟩ heq
  cases e <;> cases f
  · have hh : C ∪ D.1=C ∪ E.1 := by simpa only [orientationCode,Bool.false_eq_true,if_false] using heq
    have hd := admissible_union_injective m C a D.1 E.1 D.2 E.2 hh
    exact Prod.ext rfl (Subtype.ext hd)
  · have hh : C ∪ D.1=halfShift m C ∪ E.1 := by simp [orientationCode] at heq; exact heq
    exact False.elim (admissible_orientation_distinct m C a hC hfree D.1 E.1 D.2 E.2 hh)
  · have hh : C ∪ E.1=halfShift m C ∪ D.1 := by simp [orientationCode] at heq; exact heq.symm
    exact False.elim (admissible_orientation_distinct m C a hC hfree E.1 D.1 E.2 D.2 hh)
  · have hh : halfShift m C ∪ D.1=halfShift m C ∪ E.1 := by simp [orientationCode] at heq; exact heq
    have hD : halfShift m D.1=D.1 := by
      obtain ⟨b,hb,_,_⟩ := D.2
      rw [hb,halfShift_fibre]
    have hE : halfShift m E.1=E.1 := by
      obtain ⟨b,hb,_,_⟩ := E.2
      rw [hb,halfShift_fibre]
    have ht := congrArg (halfShift m) hh
    rw [halfShift_union,halfShift_union,halfShift_twice,hD,hE] at ht
    have hd := admissible_union_injective m C a D.1 E.1 D.2 E.2 ht
    exact Prod.ext rfl (Subtype.ext hd)

/-- Every actual collision is represented, and every code gives an actual collision. -/
theorem two_simple_fibre_code_iff (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (ha : Disjoint C (fibre (m : ZMod (2*m)) a))
    (T : Finset (ZMod (2*m))) :
    T ∈ originalFibre m (C ∪ fibre (m : ZMod (2*m)) a) ↔
      ∃ p : Bool × {D : Finset (ZMod (2*m)) // D ∈ admissibleFullPairs m C a},
        orientationCode m C a p=T := by
  rw [two_simple_fibre_rectangle m hm C a hC hfree ha]
  constructor
  · rintro (⟨D,hD,hT⟩|⟨D,hD,hT⟩)
    · exact ⟨(false,⟨D,hD⟩),by simpa only [orientationCode,Bool.false_eq_true,if_false] using hT⟩
    · exact ⟨(true,⟨D,hD⟩),by simpa only [orientationCode,if_true] using hT⟩
  · rintro ⟨⟨e,D⟩,hT⟩
    cases e
    · exact Or.inl ⟨D.1,D.2,by simpa only [orientationCode,Bool.false_eq_true,if_false] using hT⟩
    · exact Or.inr ⟨D.1,D.2,by simpa only [orientationCode,if_true] using hT⟩

/-- A genuine bijection, not just a cover by at most four candidates. -/
noncomputable def twoSimpleFibreEquiv (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hfree : AntipodalFree m C) (ha : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    (Bool × {D : Finset (ZMod (2*m)) // D ∈ admissibleFullPairs m C a}) ≃
      {T : Finset (ZMod (2*m)) // T ∈ originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)} := by
  let f : (Bool × {D : Finset (ZMod (2*m)) // D ∈ admissibleFullPairs m C a}) →
      {T : Finset (ZMod (2*m)) // T ∈ originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)} :=
    fun p => ⟨orientationCode m C a p,
      (two_simple_fibre_code_iff m hm C a hC hfree ha _).mpr ⟨p,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    exact orientationCode_injective m C a hC hfree (congrArg Subtype.val he)
  · intro T
    obtain ⟨p,hp⟩ := (two_simple_fibre_code_iff m hm C a hC hfree ha T.1).mp T.2
    exact ⟨p,Subtype.ext hp⟩



end Couret.InterIA.Fibres


