-- Prove2me | solution 1 for UnitalMagmaDefect.defect_even_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T04:59:27.498571+00:00
-- url     : https://prove2.me/submissions/c7ad3e5d-e605-43f1-aa1b-f8dafd0f21de

import Definitions.Def_Combinatorics_CodiscreteMagmaBicategory
import Definitions.Def_Combinatorics_UnitalMagmaDefect

open UnitalMagmaDefect Finset

universe u

open UnitalMagmaDefect Finset in
/-- **A commutative magma has even associativity defect**: reversing a triple is a
fixed-point-free involution on the non-associative triples. -/
theorem solution {M : Type u} [Mul M] [Fintype M] [DecidableEq M]
    (hcomm : ∀ a b : M, a * b = b * a) : Even (defect M) := by
  classical
  let e := Fintype.equivFin M
  have hmem : ∀ t : M × M × M, t ∈ defectSet M ↔ (t.1 * t.2.1) * t.2.2 ≠ t.1 * (t.2.1 * t.2.2) := by
    intro t; simp [defectSet]
  have hne : ∀ t ∈ defectSet M, t.1 ≠ t.2.2 := by
    rintro ⟨a, b, c⟩ ht hac
    simp only at hac
    subst hac
    rw [hmem] at ht
    apply ht
    show (a * b) * a = a * (b * a)
    rw [hcomm (a * b) a, hcomm b a]
  have hrev : ∀ t ∈ defectSet M, (t.2.2, t.2.1, t.1) ∈ defectSet M := by
    rintro ⟨a, b, c⟩ ht
    rw [hmem] at ht ⊢
    show (c * b) * a ≠ c * (b * a)
    intro h
    apply ht
    have h1 : (c * b) * a = a * (b * c) := by rw [hcomm (c * b) a, hcomm c b]
    have h2 : c * (b * a) = (a * b) * c := by rw [hcomm c (b * a), hcomm b a]
    rw [h1, h2] at h
    exact h.symm
  set S := defectSet M with hS
  have hcard : (S.filter (fun t => e t.1 < e t.2.2)).card
      = (S.filter (fun t => ¬ (e t.1 < e t.2.2))).card := by
    refine Finset.card_nbij' (fun t => (t.2.2, t.2.1, t.1)) (fun t => (t.2.2, t.2.1, t.1))
      ?_ ?_ ?_ ?_
    · intro t ht
      simp only [coe_filter, Set.mem_setOf_eq] at ht ⊢
      exact ⟨hrev t ht.1, lt_asymm ht.2⟩
    · intro t ht
      simp only [coe_filter, Set.mem_setOf_eq] at ht ⊢
      refine ⟨hrev t ht.1, ?_⟩
      have h1 : e t.1 ≠ e t.2.2 := fun h => hne t ht.1 (e.injective h)
      exact lt_of_le_of_ne (not_lt.mp ht.2) h1.symm
    · intro t _; rfl
    · intro t _; rfl
  unfold defect
  rw [← hS]
  rw [← Finset.filter_card_add_filter_neg_card_eq_card (fun t => e t.1 < e t.2.2), ← hcard]
  exact ⟨_, rfl⟩
