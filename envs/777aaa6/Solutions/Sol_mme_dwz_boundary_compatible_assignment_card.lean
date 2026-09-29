-- Prove2me | solution 1 for mme_dwz_boundary_compatible_assignment_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T08:35:22.299355+00:00
-- url     : https://prove2.me/submissions/3423e841-8898-4ea2-a9ef-2840e3e29c43

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.Sum
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

open BigOperators

set_option autoImplicit false

namespace MME.DWZJoint

theorem boundary_positive_partition_card
    {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [DecidableEq K] [DecidableEq L]
    (fine : A → K × L) (component : A → C) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ)
    (hsupport : ∀ a, coarse (component a) = (fine a).1)
    (hboundary : ∀ c, Boundary c → ∀ l,
      Fintype.card {a : A // component a = c ∧ (fine a).2 = l} = b c l)
    (k : K) (l : L) :
    (∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l) +
      Fintype.card {a : A // fine a = (k, l) ∧ ¬Boundary (component a)} =
        Fintype.card {a : A // fine a = (k, l)} := by
  classical
  let s : Finset A := Finset.univ.filter (fun a ↦ fine a = (k, l))
  let t : Finset C := Finset.univ.filter (fun c ↦ Boundary c ∧ coarse c = k)
  have hmaps : (↑(s.filter (fun a ↦ Boundary (component a))) : Set A).MapsTo
      component (↑t : Set C) := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hf : fine a = (k, l) := (Finset.mem_filter.mp ha'.1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ha'.2, ?_⟩
    rw [hsupport a, hf]
  have hboundaryCount : (s.filter (fun a ↦ Boundary (component a))).card =
      ∑ c ∈ t, b c l := by
    rw [Finset.card_eq_sum_card_fiberwise (f := component) hmaps]
    apply Finset.sum_congr rfl
    intro c hc
    rcases (Finset.mem_filter.mp hc).2 with ⟨hcB, hcK⟩
    have hfilter : (s.filter (fun a ↦ Boundary (component a))).filter
        (fun a ↦ component a = c) =
        Finset.univ.filter (fun a : A ↦ component a = c ∧ (fine a).2 = l) := by
      ext a
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨hf, _⟩, hcomp⟩
        exact ⟨hcomp, congrArg Prod.snd hf⟩
      · rintro ⟨hcomp, hl⟩
        refine ⟨⟨Prod.ext ?_ hl, ?_⟩, hcomp⟩
        · rw [← hsupport a, hcomp, hcK]
        · simpa only [hcomp] using hcB
    rw [hfilter]
    simpa only [Fintype.card_subtype] using hboundary c hcB l
  have hp := Finset.card_filter_add_card_filter_not
    (s := s) (fun a ↦ Boundary (component a))
  rw [hboundaryCount] at hp
  simpa only [s, t, Fintype.card_subtype, Finset.filter_filter] using hp

theorem boundary_residual_card
    {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [DecidableEq K] [DecidableEq L]
    (fine : A → K × L) (component : A → C) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ)
    (hsupport : ∀ a, coarse (component a) = (fine a).1)
    (hboundary : ∀ c, Boundary c → ∀ l,
      Fintype.card {a : A // component a = c ∧ (fine a).2 = l} = b c l)
    (k : K) (l : L) :
    (∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l) ≤
        Fintype.card {a : A // fine a = (k, l)} ∧
      Fintype.card {a : A // fine a = (k, l) ∧ ¬Boundary (component a)} =
        Fintype.card {a : A // fine a = (k, l)} -
          ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l := by
  have hp := boundary_positive_partition_card fine component coarse Boundary b hsupport hboundary k l
  omega

end MME.DWZJoint

namespace MME.DWZJoint

variable {A C K L : Type*}
variable [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
variable [DecidableEq K] [DecidableEq L]

def boundaryCollapse (coarse : C → K) (Boundary : C → Prop)
    [DecidablePred Boundary] (c : C) : C ⊕ K :=
  if Boundary c then Sum.inl c else Sum.inr (coarse c)

def boundaryJointHistogram (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ) :
    (C ⊕ K) × (K × L) → ℕ
  | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
  | (Sum.inr k', (k, l)) =>
      if k' = k then Fintype.card {a : A // fine a = (k, l)} -
        ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
      else 0

omit [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [DecidableEq K] [DecidableEq L] in
theorem boundaryCollapse_inl_iff (coarse : C → K) (Boundary : C → Prop)
    [DecidablePred Boundary] (c' c : C) :
    boundaryCollapse coarse Boundary c' = Sum.inl c ↔ c' = c ∧ Boundary c := by
  by_cases hb : Boundary c'
  · simp only [boundaryCollapse, if_pos hb, Sum.inl.injEq]
    constructor
    · intro h
      exact ⟨h, h ▸ hb⟩
    · exact And.left
  · simp only [boundaryCollapse, if_neg hb, Sum.inr_ne_inl, false_iff, not_and]
    intro h
    exact h ▸ hb

omit [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] [DecidableEq K] [DecidableEq L] in
theorem boundaryCollapse_inr_iff (coarse : C → K) (Boundary : C → Prop)
    [DecidablePred Boundary] (c : C) (k : K) :
    boundaryCollapse coarse Boundary c = Sum.inr k ↔ ¬Boundary c ∧ coarse c = k := by
  by_cases hb : Boundary c <;> simp [boundaryCollapse, hb]

theorem boundary_compatibility_iff_joint_histogram
    (fine : A → K × L) (component : A → C) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ) :
    ((∀ a, coarse (component a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // component a = c ∧ (fine a).2 = l} = b c l) ↔
      ∀ di, Fintype.card {a : A //
        (boundaryCollapse coarse Boundary (component a), fine a) = di} =
          boundaryJointHistogram fine coarse Boundary b di := by
  classical
  constructor
  · rintro ⟨hsupport, hboundary⟩ ⟨d, k, l⟩
    cases d with
    | inl c =>
      by_cases hc : Boundary c ∧ coarse c = k
      · have heq :
            Fintype.card {a : A //
              (boundaryCollapse coarse Boundary (component a), fine a) = (Sum.inl c, k, l)} =
            Fintype.card {a : A // component a = c ∧ (fine a).2 = l} := by
          apply Fintype.card_congr (Equiv.subtypeEquivRight _)
          intro a
          simp only [Prod.ext_iff, boundaryCollapse_inl_iff]
          constructor
          · rintro ⟨⟨hcomp, _⟩, _, hl⟩
            exact ⟨hcomp, hl⟩
          · rintro ⟨hcomp, hl⟩
            refine ⟨⟨hcomp, hc.1⟩, ?_, hl⟩
            rw [← hsupport a, hcomp, hc.2]
        simpa only [boundaryJointHistogram, if_pos hc] using heq.trans (hboundary c hc.1 l)
      · have heq : Fintype.card {a : A //
            (boundaryCollapse coarse Boundary (component a), fine a) = (Sum.inl c, k, l)} = 0 := by
          apply Fintype.card_eq_zero_iff.mpr
          refine ⟨fun a ↦ ?_⟩
          have hh := (Prod.ext_iff.mp a.2)
          have hh' := (boundaryCollapse_inl_iff coarse Boundary _ _).mp hh.1
          apply hc
          refine ⟨hh'.2, ?_⟩
          rw [← hh'.1, hsupport a.1]
          exact congrArg Prod.fst hh.2
        simpa only [boundaryJointHistogram, if_neg hc] using heq
    | inr k' =>
      by_cases hk : k' = k
      · subst k'
        have heq :
            Fintype.card {a : A //
              (boundaryCollapse coarse Boundary (component a), fine a) = (Sum.inr k, k, l)} =
            Fintype.card {a : A // fine a = (k, l) ∧ ¬Boundary (component a)} := by
          apply Fintype.card_congr (Equiv.subtypeEquivRight _)
          intro a
          simp only [Prod.ext_iff, boundaryCollapse_inr_iff]
          constructor
          · rintro ⟨⟨hb, _⟩, hk, hl⟩
            exact ⟨⟨hk, hl⟩, hb⟩
          · rintro ⟨⟨hk, hl⟩, hb⟩
            exact ⟨⟨hb, (hsupport a).trans hk⟩, hk, hl⟩
        simpa only [boundaryJointHistogram, if_pos rfl] using
          heq.trans (boundary_residual_card fine component coarse Boundary b hsupport hboundary k l).2
      · have heq : Fintype.card {a : A //
            (boundaryCollapse coarse Boundary (component a), fine a) = (Sum.inr k', k, l)} = 0 := by
          apply Fintype.card_eq_zero_iff.mpr
          refine ⟨fun a ↦ ?_⟩
          have hh := Prod.ext_iff.mp a.2
          have hh' := (boundaryCollapse_inr_iff coarse Boundary _ _).mp hh.1
          apply hk
          rw [← hh'.2, hsupport a.1]
          exact congrArg Prod.fst hh.2
        simpa only [boundaryJointHistogram, if_neg hk] using heq
  · intro hjoint
    have hsupport : ∀ a, coarse (component a) = (fine a).1 := by
      intro a
      by_contra hbad
      have hz := hjoint (boundaryCollapse coarse Boundary (component a), fine a)
      have hm : boundaryJointHistogram fine coarse Boundary b
          (boundaryCollapse coarse Boundary (component a), fine a) = 0 := by
        by_cases hb : Boundary (component a) <;>
          simp [boundaryCollapse, boundaryJointHistogram, hb, hbad]
      rw [hm] at hz
      have hp : 0 < Fintype.card {a' : A //
          (boundaryCollapse coarse Boundary (component a'), fine a') =
            (boundaryCollapse coarse Boundary (component a), fine a)} :=
        Fintype.card_pos_iff.mpr ⟨⟨a, rfl⟩⟩
      omega
    refine ⟨hsupport, ?_⟩
    intro c hc l
    have hz := hjoint (Sum.inl c, coarse c, l)
    have heq : Fintype.card {a : A // component a = c ∧ (fine a).2 = l} =
        Fintype.card {a : A //
          (boundaryCollapse coarse Boundary (component a), fine a) = (Sum.inl c, coarse c, l)} := by
      apply Fintype.card_congr (Equiv.subtypeEquivRight _)
      intro a
      simp only [Prod.ext_iff, boundaryCollapse_inl_iff]
      constructor
      · rintro ⟨hcomp, hl⟩
        refine ⟨⟨hcomp, hc⟩, ?_, hl⟩
        rw [← hsupport a, hcomp]
      · rintro ⟨⟨hcomp, _⟩, _, hl⟩
        exact ⟨hcomp, hl⟩
    simpa only [boundaryJointHistogram, and_self, hc, true_and, if_true] using heq.trans hz

theorem boundary_compatible_assignment_card
    [Fintype K] [Fintype L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ) (n : C → ℕ)
    (hFine : ∀ i,
      (∑ di : {di : (C ⊕ K) × (K × L) // di.2 = i},
        boundaryJointHistogram fine coarse Boundary b di.1) =
        Fintype.card {a : A // fine a = i})
    (hCollapsed : ∀ d,
      (∑ c : {c : C // boundaryCollapse coarse Boundary c = d}, n c.1) =
        ∑ i, boundaryJointHistogram fine coarse Boundary b (d, i)) :
    Nat.card {g : A → C //
      (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
      (∀ a, coarse (g a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} =
      (∏ i, (Fintype.card {a : A // fine a = i}).factorial /
        ∏ di : {di : (C ⊕ K) × (K × L) // di.2 = i},
          (boundaryJointHistogram fine coarse Boundary b di.1).factorial) *
      (∏ d, (∑ i, boundaryJointHistogram fine coarse Boundary b (d, i)).factorial /
        ∏ c : {c : C // boundaryCollapse coarse Boundary c = d}, (n c.1).factorial) := by
  classical
  have hequiv :
      {g : A → C //
        (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
        (∀ a, coarse (g a) = (fine a).1) ∧
        ∀ c, Boundary c → ∀ l,
          Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} ≃
      CompatibleAssignments fine (boundaryCollapse coarse Boundary) n
        (boundaryJointHistogram fine coarse Boundary b) :=
    Equiv.subtypeEquivRight (fun g ↦ and_congr_right (fun _ ↦
      boundary_compatibility_iff_joint_histogram fine g coarse Boundary b))
  rw [Nat.card_congr hequiv]
  exact twoStageCompatibility_card fine (boundaryCollapse coarse Boundary) n
    (boundaryJointHistogram fine coarse Boundary b) hFine hCollapsed

end MME.DWZJoint

theorem solution
    {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary] (b : C → L → ℕ) (n : C → ℕ) :
    let collapse : C → C ⊕ K :=
      fun c ↦ if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let m : (C ⊕ K) × (K × L) → ℕ
      | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
      | (Sum.inr k', (k, l)) =>
          if k' = k then Fintype.card {a : A // fine a = (k, l)} -
            ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
          else 0
    (∀ i, (∑ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, m di.1) =
      Fintype.card {a : A // fine a = i}) →
    (∀ d, (∑ c : {c : C // collapse c = d}, n c.1) = ∑ i, m (d, i)) →
    Nat.card {g : A → C //
      (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
      (∀ a, coarse (g a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} =
      (∏ i, (Fintype.card {a : A // fine a = i}).factorial /
        ∏ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, (m di.1).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ c : {c : C // collapse c = d}, (n c.1).factorial) := by
  dsimp only
  intro hFine hCollapsed
  exact MME.DWZJoint.boundary_compatible_assignment_card fine coarse Boundary b n hFine hCollapsed

