-- Prove2me | Definitions.Def_Couret_XorFibreClosure_3be6ba745ef2
-- name    : Couret_XorFibreClosure_3be6ba745ef2
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:11:30.020902+00:00
-- url     : https://prove2.me/theorems/9478fd98-85fd-4871-bdc4-a997869e9e27
-- title:
--   Ternary symmetric-difference closure
-- statement:
--   A family $P$ of finite subsets is xor-closed when $$A,B,C\in P\Longrightarrow A\triangle B\triangle C\in P.$$ This ternary closure is the affine, rather than necessarily linear, version of binary-vector closure. The bundle uses it for cyclic support fibres assembled from orientations and admissible full antipodal pairs.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/XorFibreClosure.lean; source file SHA-256 a86ebce55d2e73697b99a9d21c33602c973642d6738fd2fc71173d16937da5e2

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
import Definitions.Def_Couret_UniversalFibre_5180566b07f2

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity

/-- Intrinsic affine closure for finite binary indicators. -/
def XorClosed {α : Type*} [DecidableEq α] (P : Set (Finset α)) : Prop :=
  ∀ A ∈ P, ∀ B ∈ P, ∀ C ∈ P, symmDiff (symmDiff A B) C ∈ P

theorem small_family_xor_closed {α : Type*} [DecidableEq α] (P : Set (Finset α))
    (hP : P.ncard=1 ∨ P.ncard=2) : XorClosed P := by
  classical
  rcases hP with h|h
  · obtain ⟨A,rfl⟩ := Set.ncard_eq_one.mp h
    intro A hA B hB C hC
    simp only [Set.mem_singleton_iff] at hA hB hC ⊢
    subst A; subst B
    simpa only [symmDiff_self,bot_symmDiff] using hC
  · obtain ⟨A,B,_hAB,rfl⟩ := Set.ncard_eq_two.mp h
    intro X hX Y hY Z hZ
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hX hY hZ ⊢
    rcases hX with rfl|rfl <;> rcases hY with rfl|rfl <;> rcases hZ with rfl|rfl <;>
      simp

theorem pair_family_xor_closed {α : Type*} [DecidableEq α] (A B : Finset α) :
    XorClosed ({A,B} : Set (Finset α)) := by
  intro X hX Y hY Z hZ
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hX hY hZ ⊢
  rcases hX with rfl|rfl <;> rcases hY with rfl|rfl <;> rcases hZ with rfl|rfl <;>
    simp

theorem xor_shuffle {α : Type*} [DecidableEq α] (A B C D E F : Finset α) :
    symmDiff (symmDiff (symmDiff A D) (symmDiff B E)) (symmDiff C F)=
      symmDiff (symmDiff (symmDiff A B) C) (symmDiff (symmDiff D E) F) := by
  simp only [symmDiff_assoc]
  ac_rfl

theorem halfShift_disjoint_full (m : ℕ) (C : Finset (ZMod (2*m))) (b : ZMod (2*m))
    (hd : Disjoint C (fibre (m : ZMod (2*m)) b)) :
    Disjoint (halfShift m C) (fibre (m : ZMod (2*m)) b) := by
  apply Finset.disjoint_left.mpr
  intro x hx hf
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hback := Couret.InterIA.IntersectionTwo.stable_pair_of_antipodal b (m : ZMod (2*m))
    (Couret.InterIA.L4.half_add_half m) (y+m) hf
  have hyf : y ∈ fibre (m : ZMod (2*m)) b := by
    simpa only [add_assoc,Couret.InterIA.L4.half_add_half,add_zero] using hback
  exact Finset.disjoint_left.mp hd hy hyf

theorem orientation_disjoint_admissible (m : ℕ) (C : Finset (ZMod (2*m)))
    (a : ZMod (2*m)) (O D : Finset (ZMod (2*m)))
    (hO : O ∈ ({C,halfShift m C} : Set (Finset (ZMod (2*m)))))
    (hD : D ∈ admissibleFullPairs m C a) : Disjoint O D := by
  obtain ⟨b,rfl,hd,_⟩ := hD
  rcases hO with h|h
  · rw [h]; exact hd
  · rw [Set.mem_singleton_iff.mp h]; exact halfShift_disjoint_full m C b hd

theorem two_simple_fibre_xor_closed (m : ℕ) (hm : 0 < m)
    (C : Finset (ZMod (2*m))) (a : ZMod (2*m)) (hC : C.card=2)
    (hf : AntipodalFree m C) (hd : Disjoint C (fibre (m : ZMod (2*m)) a)) :
    XorClosed (originalFibre m (C ∪ fibre (m : ZMod (2*m)) a)) := by
  let O : Set (Finset (ZMod (2*m))) := {C,halfShift m C}
  let P := admissibleFullPairs m C a
  have hP : XorClosed P := by
    rcases admissible_full_pairs_one_or_two m hm C hC a hd with h|⟨D,hDa,h⟩
    · rw [show P={fibre (m : ZMod (2*m)) a} from h]
      simpa only [Set.insert_eq_of_mem (Set.mem_singleton _)] using pair_family_xor_closed (fibre (m : ZMod (2*m)) a) (fibre (m : ZMod (2*m)) a)
    · rw [show P={fibre (m : ZMod (2*m)) a,D} from h]
      exact pair_family_xor_closed _ _
  have hO : XorClosed O := pair_family_xor_closed _ _
  have hrep : ∀ T, T ∈ originalFibre m (C ∪ fibre (m : ZMod (2*m)) a) ↔
      ∃ U ∈ O, ∃ D ∈ P, T=symmDiff U D := by
    intro T
    rw [two_simple_fibre_rectangle m hm C a hC hf hd]
    constructor
    · rintro (⟨D,hD,rfl⟩|⟨D,hD,rfl⟩)
      · exact ⟨C,Or.inl rfl,D,hD,(Finset.symmDiff_eq_union (orientation_disjoint_admissible m C a C D (Or.inl rfl) hD)).symm⟩
      · exact ⟨halfShift m C,Or.inr (Set.mem_singleton _),D,hD,
          (Finset.symmDiff_eq_union (orientation_disjoint_admissible m C a (halfShift m C) D (Or.inr (Set.mem_singleton _)) hD)).symm⟩
    · rintro ⟨U,hU,D,hD,rfl⟩
      rw [Finset.symmDiff_eq_union (orientation_disjoint_admissible m C a U D hU hD)]
      rcases hU with h|h
      · rw [h]; exact Or.inl ⟨D,hD,rfl⟩
      · rw [Set.mem_singleton_iff.mp h]; exact Or.inr ⟨D,hD,rfl⟩
  intro T hT U hU V hV
  obtain ⟨A,hA,D,hD,rfl⟩ := (hrep T).mp hT
  obtain ⟨B,hB,E,hE,rfl⟩ := (hrep U).mp hU
  obtain ⟨K,hK,F,hF,rfl⟩ := (hrep V).mp hV
  apply (hrep _).mpr
  exact ⟨_,hO A hA B hB K hK,_,hP D hD E hE F hF,xor_shuffle A B K D E F⟩

theorem cyclic_four_fibre_xor_closed (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=4) : XorClosed (cyclicFourFibre n S) := by
  classical
  rcases Nat.even_or_odd n with he|ho
  · obtain ⟨m,hm⟩ := he
    have hn2 : n=2*m := by omega
    clear hm
    subst n
    have hm : 0 < m := by omega
    rcases even_four_support_cases m hm S hS with hf|hs|⟨C,a,hC,hf,hd,hSe⟩
    · rw [show cyclicFourFibre (2*m) S={S,S.image (fun x => x+(m : ZMod (2*m)))} from antipodal_free_four_fibre_eq_pair m hm S hS hf]
      exact pair_family_xor_closed _ _
    · exact small_family_xor_closed _ (stable_four_fibre_ncard m hm S hS hs)
    · rw [hSe]
      exact two_simple_fibre_xor_closed m hm C a hC hf hd
  · rw [odd_four_fibre_singleton n ho S hS]
    simpa only [Set.insert_eq_of_mem (Set.mem_singleton _)] using pair_family_xor_closed S S

end Couret.InterIA.Fibres


