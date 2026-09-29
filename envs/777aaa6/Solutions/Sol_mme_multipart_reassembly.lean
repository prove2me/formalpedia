-- Prove2me | solution 1 for mme_multipart_reassembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-23T06:24:41.210166+00:00
-- url     : https://prove2.me/submissions/4b57463e-1f95-4985-872f-e7bf3ea68067

import Mathlib
import Theorems.Thm_mme_multipart_card_split

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u


namespace MME.MultiSplit

/-- Per-part histogram bounds reassemble into a global one. -/
theorem count_within {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (P : B → Prop)
    (target e : Fin p → ℝ)
    (h : ∀ j, |(Fintype.card {b : B // part b = j ∧ P b} : ℝ) - target j| ≤ e j) :
    |(Fintype.card {b : B // P b} : ℝ) - ∑ j, target j| ≤ ∑ j, e j := by
  classical
  have hcard : (Fintype.card {b : B // P b} : ℝ) =
      ∑ j, (Fintype.card {b : B // part b = j ∧ P b} : ℝ) := by
    rw [← Nat.cast_sum, mme_multipart_card_split part P]
  rw [hcard, ← Finset.sum_sub_distrib]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact Finset.sum_le_sum (fun j _ ↦ h j)

/-- Per-part grade agreement reassembles into a global one. -/
theorem forall_parts {B : Type u} {p : ℕ} (part : B → Fin p) (Q : B → Prop)
    (h : ∀ j, ∀ b, part b = j → Q b) : ∀ b, Q b :=
  fun b ↦ h (part b) b rfl


end MME.MultiSplit

theorem solution :
    (∀ {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (P : B → Prop)
      (target e : Fin p → ℝ),
      (∀ j, |(Fintype.card {b : B // part b = j ∧ P b} : ℝ) - target j| ≤ e j) →
      |(Fintype.card {b : B // P b} : ℝ) - ∑ j, target j| ≤ ∑ j, e j) ∧
    ∀ {B : Type u} {p : ℕ} (part : B → Fin p) (Q : B → Prop),
      (∀ j, ∀ b, part b = j → Q b) → ∀ b, Q b :=
  ⟨fun {B} _ {p} part P target e h ↦ MME.MultiSplit.count_within part P target e h,
   fun {B} {p} part Q h ↦ MME.MultiSplit.forall_parts part Q h⟩
