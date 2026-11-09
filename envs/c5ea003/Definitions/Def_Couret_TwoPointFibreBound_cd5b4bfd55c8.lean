-- Prove2me | Definitions.Def_Couret_TwoPointFibreBound_cd5b4bfd55c8
-- name    : Couret_TwoPointFibreBound_cd5b4bfd55c8
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:09:54.783342+00:00
-- url     : https://prove2.me/theorems/34758e4c-8c7d-48b2-995d-d922dcaadd63
-- title:
--   Two-point cyclic square fibres
-- statement:
--   Defines the square-profile fibre of a support modulo $n$ restricted to supports of size two. Includes proved classifications and uniqueness of any alternative partner for positive cyclic modulus, yielding fibre size one or two. Handles even modulus through half-turn geometry and odd modulus through square-profile injectivity.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoPointFibreBound.lean; source file SHA-256 e6ffec2f521b035b477a11bcea69e1f9fc11afb2bff6c576d1a5a38de1b2eb19

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
import Definitions.Def_Couret_TwoSimpleFibre_28201a278c39

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.TwoPoint

def pairFibre (n : ℕ) (S : Finset (ZMod n)) : Set (Finset (ZMod n)) :=
  {T | T.card=2 ∧ ∀ z, orderedSquare S z=orderedSquare T z}

theorem pair_profiles_match_double {G : Type*} [AddCommGroup G] [DecidableEq G]
    (a b c d : G) (hab : a ≠ b) (hd : a+a ≠ b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    c+c=a+a ∨ d+d=a+a := by
  have hp := heq (a+a)
  rw [pair_coeff_at_double_distinct a b hab hd] at hp
  by_contra hn
  have hc : c+c ≠ a+a := by tauto
  have hd' : d+d ≠ a+a := by tauto
  simp only [pairCoeff,if_neg hc,if_neg hd',zero_add] at hp
  (split_ifs at hp; omega)

theorem matched_even_pair_is_half_translate (m : ℕ) (hm : 0 < m)
    (a b c d : ZMod (2*m)) (hab : a ≠ b) (hd : a+a ≠ b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) (hc : c+c=a+a) :
    ({c,d} : Finset (ZMod (2*m)))={a,b} ∨
      ({c,d} : Finset (ZMod (2*m)))=halfShift m {a,b} := by
  have hs := matched_double_forces_center a b c d hab hd heq hc
  rcases (even_double_fibre m hm a c).mp hc with hc|hc
  · subst c
    have hd' : d=b := add_left_cancel hs
    exact Or.inl (by rw [hd'])
  · have hpair : (a+(m : ZMod (2*m)))+(b+m)=a+b := by
      calc _ = (a+b)+((m : ZMod (2*m))+m) := by abel
           _ = a+b := by rw [Couret.InterIA.L4.half_add_half,add_zero]
    rw [hc] at hs
    have hd' : d=b+(m : ZMod (2*m)) := add_left_cancel (hs.trans hpair.symm)
    exact Or.inr (by simp [halfShift,hc,hd'])

theorem even_pair_distinct_doubles_collision (m : ℕ) (hm : 0 < m)
    (a b c d : ZMod (2*m)) (hab : a ≠ b) (hd : a+a ≠ b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) :
    ({c,d} : Finset (ZMod (2*m)))={a,b} ∨
      ({c,d} : Finset (ZMod (2*m)))=halfShift m {a,b} := by
  rcases pair_profiles_match_double a b c d hab hd heq with hc|hd'
  · exact matched_even_pair_is_half_translate m hm a b c d hab hd heq hc
  · have heq' : ∀ z, pairCoeff a b z=pairCoeff d c z := by
      intro z; exact (heq z).trans (pair_coeff_comm c d z)
    simpa only [Finset.pair_comm c d] using
      matched_even_pair_is_half_translate m hm a b d c hab hd heq' hd'

theorem antipodal_pairs_eq_of_double (m : ℕ) (hm : 0 < m) (a b : ZMod (2*m))
    (he : a+a=b+b) : fibre (m : ZMod (2*m)) a=fibre (m : ZMod (2*m)) b := by
  rcases (even_double_fibre m hm b a).mp he with h|h
  · rw [h]
  · rw [h]
    exact fibre_partner (m : ZMod (2*m)) b (Couret.InterIA.L4.half_add_half m)

theorem even_equal_double_partner (m : ℕ) (hm : 0 < m)
    (a b : ZMod (2*m)) (hab : a ≠ b) (hd : a+a=b+b) : b=a+m := by
  rcases (even_double_fibre m hm a b).mp hd.symm with hb|hb
  · exact False.elim (hab hb.symm)
  · exact hb

/-- A different antipodal pair must occupy the other diagonal position of the profile. -/
theorem even_antipodal_alternative_double (m : ℕ) (hm : 0 < m)
    (a b c d : ZMod (2*m)) (hab : a ≠ b) (hcd : c ≠ d) (hd : a+a=b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z)
    (hne : ({c,d} : Finset (ZMod (2*m))) ≠ {a,b}) :
    c+c=a+b ∧ d=c+m := by
  have hD := equal_doubles_transfer a b c d hcd hd heq
  have hb := even_equal_double_partner m hm a b hab hd
  have hdc := even_equal_double_partner m hm c d hcd hD
  have hp : pairCoeff a b (c+c)=2 := by
    rw [heq,pair_coeff_at_double_equal c d hcd hD]
  refine ⟨?_,hdc⟩
  rcases equal_doubles_positions a b (c+c) hd hp with h|h
  · have hf := antipodal_pairs_eq_of_double m hm c a h.symm
    apply False.elim
    apply hne
    simpa only [fibre,← hb,← hdc] using hf
  · exact h.symm

/-- In an even cyclic group, every two-point fibre has at most one different member. -/
theorem even_pair_fibre_unique_other (m : ℕ) (hm : 0 < m)
    (S T U : Finset (ZMod (2*m))) (hS : S.card=2) (hT : T.card=2) (hU : U.card=2)
    (hST : ∀ z, orderedSquare S z=orderedSquare T z)
    (hSU : ∀ z, orderedSquare S z=orderedSquare U z) (hTS : T ≠ S) (hUS : U ≠ S) : T=U := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  obtain ⟨c,d,hcd,rfl⟩ := Finset.card_eq_two.mp hT
  obtain ⟨e,f,hef,rfl⟩ := Finset.card_eq_two.mp hU
  have h1 : ∀ z, pairCoeff a b z=pairCoeff c d z := by
    intro z; simpa only [actual_pair_coefficient a b z hab,actual_pair_coefficient c d z hcd] using hST z
  have h2 : ∀ z, pairCoeff a b z=pairCoeff e f z := by
    intro z; simpa only [actual_pair_coefficient a b z hab,actual_pair_coefficient e f z hef] using hSU z
  by_cases hd : a+a=b+b
  · obtain ⟨hc,hdc⟩ := even_antipodal_alternative_double m hm a b c d hab hcd hd h1 hTS
    obtain ⟨he,hfe⟩ := even_antipodal_alternative_double m hm a b e f hab hef hd h2 hUS
    have hfibre := antipodal_pairs_eq_of_double m hm c e (hc.trans he.symm)
    simpa only [fibre,← hdc,← hfe] using hfibre
  · have ht := (even_pair_distinct_doubles_collision m hm a b c d hab hd h1).resolve_left hTS
    have hu := (even_pair_distinct_doubles_collision m hm a b e f hab hd h2).resolve_left hUS
    exact ht.trans hu.symm

theorem cyclic_pair_fibre_unique_other (n : ℕ) (hn : 0 < n)
    (S T U : Finset (ZMod n)) (hS : S.card=2) (hT : T.card=2) (hU : U.card=2)
    (hST : ∀ z, orderedSquare S z=orderedSquare T z)
    (hSU : ∀ z, orderedSquare S z=orderedSquare U z) (hTS : T ≠ S) (hUS : U ≠ S) : T=U := by
  rcases Nat.even_or_odd n with he|ho
  · obtain ⟨m,hm⟩ := he
    have hn2 : n=2*m := by omega
    clear hm
    subst n
    exact even_pair_fibre_unique_other m (by omega) S T U hS hT hU hST hSU hTS hUS
  · exact False.elim (hTS (odd_cyclic_square_injective n ho S T hST).symm)

theorem rooted_set_one_or_two {α : Type*} (P : Set α) (a : α) (ha : a ∈ P)
    (hu : ∀ x ∈ P, ∀ y ∈ P, x ≠ a → y ≠ a → x=y) :
    P={a} ∨ ∃ b : α, b ≠ a ∧ P={a,b} := by
  classical
  by_cases hall : ∀ x ∈ P, x=a
  · left
    ext x
    constructor
    · intro hx; exact Set.mem_singleton_iff.mpr (hall x hx)
    · intro hx; rw [Set.mem_singleton_iff.mp hx]; exact ha
  · push Not at hall
    obtain ⟨b,hb,hba⟩ := hall
    refine Or.inr ⟨b,hba,?_⟩
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      by_cases hxa : x=a
      · exact Or.inl hxa
      · exact Or.inr (hu x hx b hb hxa hba)
    · rintro (rfl|rfl)
      · exact ha
      · exact hb

theorem cyclic_pair_fibre_one_or_two (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=2) :
    pairFibre n S={S} ∨ ∃ T : Finset (ZMod n), T ≠ S ∧ pairFibre n S={S,T} := by
  apply rooted_set_one_or_two (pairFibre n S) S ⟨hS,fun _ => rfl⟩
  intro T hT U hU hTS hUS
  exact cyclic_pair_fibre_unique_other n hn S T U hS hT.1 hU.1 hT.2 hU.2 hTS hUS

theorem cyclic_pair_fibre_ncard (n : ℕ) (hn : 0 < n)
    (S : Finset (ZMod n)) (hS : S.card=2) :
    (pairFibre n S).ncard=1 ∨ (pairFibre n S).ncard=2 := by
  rcases cyclic_pair_fibre_one_or_two n hn S hS with h|⟨T,hTS,h⟩
  · exact Or.inl (by rw [h,Set.ncard_singleton])
  · exact Or.inr (by rw [h,Set.ncard_pair hTS.symm])

end Couret.InterIA.Fibres


