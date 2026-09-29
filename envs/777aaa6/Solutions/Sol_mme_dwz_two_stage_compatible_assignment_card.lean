-- Prove2me | solution 1 for mme_dwz_two_stage_compatible_assignment_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:24:09.458518+00:00
-- url     : https://prove2.me/submissions/f58e4296-17a3-4129-83a3-1e9125683ee6

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

open BigOperators

set_option autoImplicit false

namespace MME.DWZJoint

variable {α β δ ι : Type*}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable [Fintype δ] [DecidableEq δ] [Fintype ι] [DecidableEq ι]

omit [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype δ] in
theorem card_fst_fiber (h : α → δ × ι) (d : δ) :
    Fintype.card {a : α // (h a).1 = d} =
      ∑ i, Fintype.card {a : α // h a = (d, i)} := by
  classical
  simp only [Fintype.card_subtype]
  have hp := Finset.card_eq_sum_card_fiberwise
    (s := Finset.univ.filter (fun a : α ↦ (h a).1 = d))
    (t := Finset.univ) (f := fun a ↦ (h a).2) ((fun _ _ ↦ Finset.mem_univ _) :
      (↑(Finset.univ.filter (fun a : α ↦ (h a).1 = d)) : Set α).MapsTo
        (fun a ↦ (h a).2) (↑(Finset.univ : Finset ι)))
  simpa only [Finset.filter_filter, Prod.ext_iff] using hp

abbrev CollapsedAssignments (fine : α → ι) (m : δ × ι → ℕ) :=
  {h : α → δ × ι // (∀ a, (h a).2 = fine a) ∧
    ∀ di, Fintype.card {a : α // h a = di} = m di}

abbrev Refinements (collapse : β → δ) (n : β → ℕ)
    (h : α → δ × ι) :=
  {g : α → β // (∀ a, collapse (g a) = (h a).1) ∧
    ∀ b, Fintype.card {a : α // g a = b} = n b}

abbrev CompatibleAssignments (fine : α → ι) (collapse : β → δ)
    (n : β → ℕ) (m : δ × ι → ℕ) :=
  {g : α → β // (∀ b, Fintype.card {a : α // g a = b} = n b) ∧
    ∀ di, Fintype.card {a : α // (collapse (g a), fine a) = di} = m di}

noncomputable def twoStageCompatibilityEquiv
    (fine : α → ι) (collapse : β → δ) (n : β → ℕ) (m : δ × ι → ℕ) :
    CompatibleAssignments fine collapse n m ≃
      Σ h : CollapsedAssignments fine m, Refinements collapse n h.1 where
  toFun g := ⟨⟨fun a ↦ (collapse (g.1 a), fine a),
    ⟨fun _ ↦ rfl, g.2.2⟩⟩, ⟨g.1, ⟨fun _ ↦ rfl, g.2.1⟩⟩⟩
  invFun z := ⟨z.2.1, ⟨z.2.2.2, by
    have heq : (fun a ↦ (collapse (z.2.1 a), fine a)) = z.1.1 := by
      funext a
      exact Prod.ext (z.2.2.1 a) (z.1.2.1 a).symm
    intro di
    change Fintype.card {a : α // (fun a ↦ (collapse (z.2.1 a), fine a)) a = di} = _
    simpa only [← heq] using z.1.2.2 di⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv z := by
    apply Sigma.ext
    · apply Subtype.ext
      funext a
      exact Prod.ext (z.2.2.1 a) (z.1.2.1 a).symm
    · apply (Subtype.heq_iff_coe_eq _).2
      · rfl
      · intro g
        change ((∀ a, collapse (g a) = collapse (z.2.1 a)) ∧ _) ↔
          ((∀ a, collapse (g a) = (z.1.1 a).1) ∧ _)
        simp only [z.2.2.1]

theorem twoStageCompatibility_card
    (fine : α → ι) (collapse : β → δ) (n : β → ℕ) (m : δ × ι → ℕ)
    (hFine : ∀ i, (∑ di : {di : δ × ι // di.2 = i}, m di.1) =
      Fintype.card {a : α // fine a = i})
    (hCollapsed : ∀ d, (∑ b : {b : β // collapse b = d}, n b.1) =
      ∑ i, m (d, i)) :
    Nat.card (CompatibleAssignments fine collapse n m) =
      (∏ i, (Fintype.card {a : α // fine a = i}).factorial /
        ∏ di : {di : δ × ι // di.2 = i}, (m di.1).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ b : {b : β // collapse b = d}, (n b.1).factorial) := by
  classical
  have hFirst := mme_fintype_constrained_prescribed_fiber_function_card
    fine Prod.snd m hFine
  have hRow (h : CollapsedAssignments fine m) (d : δ) :
      Fintype.card {a : α // (h.1 a).1 = d} = ∑ i, m (d, i) := by
    rw [card_fst_fiber]
    exact Finset.sum_congr rfl (fun i _ ↦ h.2.2 (d, i))
  have hSecond (h : CollapsedAssignments fine m) :
      Nat.card (Refinements collapse n h.1) =
        ∏ d, (∑ i, m (d, i)).factorial /
          ∏ b : {b : β // collapse b = d}, (n b.1).factorial := by
    have hc := mme_fintype_constrained_prescribed_fiber_function_card
      (fun a ↦ (h.1 a).1) collapse n (fun d ↦ (hCollapsed d).trans (hRow h d).symm)
    simpa only [Refinements, hRow] using hc
  rw [Nat.card_congr (twoStageCompatibilityEquiv fine collapse n m)]
  rw [Nat.card_sigma]
  simp only [hSecond, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card]
  exact congrArg (fun t ↦ t * _) hFirst

end MME.DWZJoint

theorem solution
    {α β δ ι : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype δ] [DecidableEq δ] [Fintype ι] [DecidableEq ι]
    (fine : α → ι) (collapse : β → δ) (n : β → ℕ) (m : δ × ι → ℕ)
    (hFine : ∀ i, (∑ di : {di : δ × ι // di.2 = i}, m di.1) =
      Fintype.card {a : α // fine a = i})
    (hCollapsed : ∀ d, (∑ b : {b : β // collapse b = d}, n b.1) =
      ∑ i, m (d, i)) :
    Nat.card {g : α → β //
      (∀ b, Fintype.card {a : α // g a = b} = n b) ∧
      ∀ di, Fintype.card {a : α // (collapse (g a), fine a) = di} = m di} =
      (∏ i, (Fintype.card {a : α // fine a = i}).factorial /
        ∏ di : {di : δ × ι // di.2 = i}, (m di.1).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ b : {b : β // collapse b = d}, (n b.1).factorial) := by
  exact MME.DWZJoint.twoStageCompatibility_card fine collapse n m hFine hCollapsed

