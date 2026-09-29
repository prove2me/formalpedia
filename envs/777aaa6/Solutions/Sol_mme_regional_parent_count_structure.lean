-- Prove2me | solution 1 for mme_regional_parent_count_structure
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T20:52:04.900272+00:00
-- url     : https://prove2.me/submissions/a8de2d6c-67dc-4d44-95f8-0b08c0a96d7e

import Definitions.Def_mme_recursive_yz_hash_filter
import Mathlib
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

private theorem row_sum {P C W : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (f : P → W) (c : C) :
    ∑ w, count cell f c w = Fintype.card {t : P // cell t = c} := by
  classical
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun t : P ↦ cell t = c)) (t := (Finset.univ : Finset W))
    (f := f) (fun _ _ ↦ Finset.mem_univ _)
  convert hc.symm using 1 <;>
    simp only [count,Finset.filter_filter,Fintype.card_subtype]

theorem solution {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hg : Graded htotal i a f) : ∀ r,
    (∀ j, ∑ w, parentCounts (RecursiveXHash.block i a) f r j w =
      RecursiveThinSplit.count (RecursiveXHash.block i a r) j) ∧
    (∀ w, ∑ j, parentCounts (RecursiveXHash.block i a) f r j w =
      Fintype.card {t : Fin (n r) // ∀ h, f ⟨r,t,h⟩ = w h}) ∧
    (∑ j, ∑ w, parentCounts (RecursiveXHash.block i a) f r j w = n r) ∧
    (∀ w j k, parentCounts (RecursiveXHash.block i a) f r j w ≠ 0 →
      parentCounts (RecursiveXHash.block i a) f r k w ≠ 0 → j = k) := by
  classical
  intro r
  have hr j := row_sum (RecursiveXHash.block i a r) (parentWord f r) j
  have hc w : ∑ j, parentCounts (RecursiveXHash.block i a) f r j w =
      Fintype.card {t : Fin (n r) // ∀ h, f ⟨r,t,h⟩ = w h} := by
    have hh := row_sum (parentWord f r) (RecursiveXHash.block i a r) w
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro j _
      unfold parentCounts count
      apply congrArg Finset.card
      ext t
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    · simp only [Fintype.card_subtype,parentWord,funext_iff]
  refine ⟨?_,hc,?_,?_⟩
  · intro j
    simpa only [parentCounts,Fintype.card_subtype,RecursiveThinSplit.count] using hr j
  · have hr' : ∀ j, (∑ w, parentCounts (RecursiveXHash.block i a) f r j w) =
        Nat.card {t : Fin (n r) // RecursiveXHash.block i a r t = j} := by
      intro j; simpa only [parentCounts,← Nat.card_eq_fintype_card] using hr j
    simp_rw [hr',Nat.card_eq_fintype_card]
    rw [← Fintype.card_sigma]
    simpa using Fintype.card_congr (Equiv.sigmaFiberEquiv (RecursiveXHash.block i a r))
  · intro w j k hj hk
    unfold parentCounts count at hj hk
    obtain ⟨t,ht⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hj)
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hk)
    have ht' : RecursiveXHash.block i a r t = j ∧ parentWord f r t = w :=
      by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using ht
    have hu' : RecursiveXHash.block i a r u = k ∧ parentWord f r u = w :=
      by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hu
    have hgt := hg ⟨r,t,0⟩
    have hgu := hg ⟨r,u,0⟩
    have hwords : f ⟨r,t,0⟩ = f ⟨r,u,0⟩ :=
      (congrFun ht'.2 0).trans (congrFun hu'.2 0).symm
    rw [hwords] at hgt
    have hjk : (j : ℕ) = (k : ℕ) := by
      rw [← ht'.1,← hu'.1]
      simpa only [fullCell,ite_true,RecursiveXHash.block] using hgt.symm.trans hgu
    exact Fin.ext hjk
