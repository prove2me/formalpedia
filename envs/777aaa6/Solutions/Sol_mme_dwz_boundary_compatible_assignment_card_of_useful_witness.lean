-- Prove2me | solution 1 for mme_dwz_boundary_compatible_assignment_card_of_useful_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T20:39:22.158555+00:00
-- url     : https://prove2.me/submissions/e6f31e70-8591-4ce7-b9ad-ea7c8e4bad79

import Theorems.Thm_mme_dwz_boundary_compatible_assignment_card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic

open scoped BigOperators
set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZUsefulWitnessCompatibility

theorem sum_joint_pred {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq C] (g : A → C) (Q : C → Prop) [DecidablePred Q]
    (P : A → Prop) [DecidablePred P] :
    (∑ c : {c : C // Q c}, Fintype.card {a : A // g a = c.val ∧ P a}) =
      Fintype.card {a : A // Q (g a) ∧ P a} := by
  classical
  let e : (Σ c : {c : C // Q c}, {a : A // g a = c.val ∧ P a}) ≃
      {a : A // Q (g a) ∧ P a} := {
    toFun := fun x ↦ ⟨x.2.val, x.2.property.1.symm ▸ x.1.property, x.2.property.2⟩
    invFun := fun a ↦ ⟨⟨g a.val, a.property.1⟩, ⟨a.val, rfl, a.property.2⟩⟩
    left_inv := by
      rintro ⟨⟨c, hc⟩, ⟨a, ha, hp⟩⟩
      cases ha
      rfl
    right_inv := fun _ ↦ rfl }
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

theorem sum_joint {A D I : Type*} [Fintype A] [Fintype D]
    [DecidableEq D] [DecidableEq I] (f : A → D) (g : A → I) (i : I) :
    (∑ d, Fintype.card {a : A // f a = d ∧ g a = i}) =
      Fintype.card {a : A // g a = i} := by
  classical
  let e : (Σ d : D, {a : A // f a = d ∧ g a = i}) ≃
      {a : A // g a = i} := {
    toFun := fun x ↦ ⟨x.2.val, x.2.property.2⟩
    invFun := fun a ↦ ⟨f a.val, ⟨a.val, rfl, a.property⟩⟩
    left_inv := by
      rintro ⟨d, ⟨a, ha, hi⟩⟩
      cases ha
      rfl
    right_inv := fun _ ↦ rfl }
  simpa only [Fintype.card_sigma] using Fintype.card_congr e

theorem witness_balances {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary]
    (g0 : A → C) (hcoarse : ∀ a, coarse (g0 a) = (fine a).1) :
    let n : C → ℕ := fun c ↦ Fintype.card {a : A // g0 a = c}
    let b : C → L → ℕ := fun c l ↦
      Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l}
    let collapse : C → C ⊕ K := fun c ↦
      if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let m : (C ⊕ K) × (K × L) → ℕ
      | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
      | (Sum.inr k', (k, l)) =>
          if k' = k then Fintype.card {a : A // fine a = (k, l)} -
            ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
          else 0
    (∀ i, (∑ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, m di.val) =
      Fintype.card {a : A // fine a = i}) ∧
    (∀ d, (∑ c : {c : C // collapse c = d}, n c.val) = ∑ i, m (d, i)) := by
  classical
  dsimp only
  let collapse : C → C ⊕ K := fun c ↦
    if Boundary c then Sum.inl c else Sum.inr (coarse c)
  let joint (d : C ⊕ K) (i : K × L) :=
    Fintype.card {a : A // collapse (g0 a) = d ∧ fine a = i}
  let m : (C ⊕ K) × (K × L) → ℕ
    | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then
        Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l} else 0
    | (Sum.inr k', (k, l)) => if k' = k then
        Fintype.card {a : A // fine a = (k, l)} -
          ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k),
            Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l}
        else 0
  change (∀ i, (∑ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, m di.val) =
      Fintype.card {a : A // fine a = i}) ∧
    (∀ d, (∑ c : {c : C // collapse c = d}, Fintype.card {a : A // g0 a = c.val}) =
      ∑ i, m (d, i))
  have hb (k : K) (l : L) :
      (∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k),
        Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l}) =
      Fintype.card {a : A // Boundary (g0 a) ∧ fine a = (k, l)} := by
    rw [Finset.sum_subtype _ (p := fun c ↦ Boundary c ∧ coarse c = k) (by simp)]
    rw [sum_joint_pred]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro a
    rw [hcoarse a]
    simp only [Prod.ext_iff]
    tauto
  have hm (d : C ⊕ K) (i : K × L) : m (d,i) = joint d i := by
    rcases i with ⟨k,l⟩
    cases d with
    | inl c =>
      dsimp only [m]
      by_cases hc : Boundary c ∧ coarse c = k
      · rw [if_pos hc]
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro a
        constructor
        · rintro ⟨ha, hl⟩
          refine ⟨?_, Prod.ext ?_ hl⟩
          · simp [collapse, ha, hc.1]
          · rw [← hcoarse a, ha, hc.2]
        · rintro ⟨ha, hi⟩
          have hg : g0 a = c := by
            by_cases hbd : Boundary (g0 a)
            · simpa [collapse, hbd] using ha
            · simp [collapse, hbd] at ha
          exact ⟨hg, congrArg Prod.snd hi⟩
      · rw [if_neg hc]
        symm
        apply Fintype.card_eq_zero_iff.mpr
        refine ⟨?_⟩
        intro a
        apply hc
        have hg : g0 a.val = c := by
          by_cases hbd : Boundary (g0 a.val) <;>
            simpa [collapse, hbd] using a.property.1
        have hbd : Boundary (g0 a.val) := by
          by_contra hn
          simpa [collapse, hn] using a.property.1
        exact ⟨hg ▸ hbd, by rw [← hg, hcoarse a.val, a.property.2]⟩
    | inr k' =>
      dsimp only [m]
      by_cases hk : k' = k
      · subst k'
        rw [if_pos rfl, hb]
        have hpartition := Finset.card_filter_add_card_filter_not
          (s := Finset.univ.filter (fun a : A ↦ fine a = (k,l)))
          (fun a ↦ Boundary (g0 a))
        have hc : Fintype.card {a : A // Boundary (g0 a) ∧ fine a = (k,l)} +
            joint (Sum.inr k) (k,l) = Fintype.card {a : A // fine a = (k,l)} := by
          have hj : joint (Sum.inr k) (k,l) =
              Fintype.card {a : A // ¬Boundary (g0 a) ∧ fine a = (k,l)} := by
            apply Fintype.card_congr
            apply Equiv.subtypeEquivRight
            intro a
            by_cases hbd : Boundary (g0 a)
            · simp [collapse, hbd]
            · simp [collapse, hbd, hcoarse a, Prod.ext_iff]
          rw [hj]
          simpa only [Fintype.card_subtype, Finset.filter_filter, and_comm] using hpartition
        exact Nat.sub_eq_of_eq_add (by simpa only [Nat.add_comm] using hc.symm)
      · rw [if_neg hk]
        symm
        apply Fintype.card_eq_zero_iff.mpr
        refine ⟨?_⟩
        rintro ⟨a, hd, hi⟩
        apply hk
        have hc : coarse (g0 a) = k' := by
          by_cases hbd : Boundary (g0 a)
          · simp [collapse, hbd] at hd
          · simpa [collapse, hbd] using hd
        rw [← hc, hcoarse a, hi]
  have hm' (di : (C ⊕ K) × (K × L)) : m di = joint di.1 di.2 := hm di.1 di.2
  constructor
  · intro i
    simp_rw [hm']
    let e : {di : (C ⊕ K) × (K × L) // di.2 = i} ≃ (C ⊕ K) := {
      toFun := fun di ↦ di.val.1
      invFun := fun d ↦ ⟨(d,i),rfl⟩
      left_inv := by rintro ⟨⟨d,i'⟩,h⟩; dsimp at h; subst i'; rfl
      right_inv := fun _ ↦ rfl }
    calc
      _ = ∑ d, joint d i := Fintype.sum_equiv e _ _
        (fun di ↦ by change joint di.val.1 di.val.2 = joint di.val.1 i; rw [di.property])
      _ = _ := sum_joint (fun a ↦ collapse (g0 a)) fine i
  · intro d
    simp_rw [hm]
    have hn := sum_joint_pred g0 (fun c ↦ collapse c = d) (fun _ ↦ True)
    simp only [and_true] at hn
    rw [hn]
    symm
    have hj := sum_joint fine (fun a ↦ collapse (g0 a)) d
    convert hj using 1
    apply Finset.sum_congr rfl
    intro i _
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ ↦ and_comm))

theorem compatible_assignment_card_of_witness {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary]
    (g0 : A → C) (hcoarse : ∀ a, coarse (g0 a) = (fine a).1) :
    let n : C → ℕ := fun c ↦ Fintype.card {a : A // g0 a = c}
    let b : C → L → ℕ := fun c l ↦
      Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l}
    let collapse : C → C ⊕ K :=
      fun c ↦ if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let m : (C ⊕ K) × (K × L) → ℕ
      | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
      | (Sum.inr k', (k, l)) =>
          if k' = k then Fintype.card {a : A // fine a = (k, l)} -
            ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
          else 0
    Nat.card {g : A → C //
      (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
      (∀ a, coarse (g a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} =
      (∏ i, (Fintype.card {a : A // fine a = i}).factorial /
        ∏ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, (m di.val).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ c : {c : C // collapse c = d}, (n c.val).factorial) := by
  classical
  have hbal := witness_balances fine coarse Boundary g0 hcoarse
  exact mme_dwz_boundary_compatible_assignment_card fine coarse Boundary
    (fun c l ↦ Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l})
    (fun c ↦ Fintype.card {a : A // g0 a = c}) hbal.1 hbal.2

end MME.DWZUsefulWitnessCompatibility

theorem solution {A C K L : Type*}
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C]
    [Fintype K] [DecidableEq K] [Fintype L] [DecidableEq L]
    (fine : A → K × L) (coarse : C → K)
    (Boundary : C → Prop) [DecidablePred Boundary]
    (g0 : A → C) (hcoarse : ∀ a, coarse (g0 a) = (fine a).1) :
    let n : C → ℕ := fun c ↦ Fintype.card {a : A // g0 a = c}
    let b : C → L → ℕ := fun c l ↦
      Fintype.card {a : A // g0 a = c ∧ (fine a).2 = l}
    let collapse : C → C ⊕ K :=
      fun c ↦ if Boundary c then Sum.inl c else Sum.inr (coarse c)
    let m : (C ⊕ K) × (K × L) → ℕ
      | (Sum.inl c, (k, l)) => if Boundary c ∧ coarse c = k then b c l else 0
      | (Sum.inr k', (k, l)) =>
          if k' = k then Fintype.card {a : A // fine a = (k, l)} -
            ∑ c ∈ Finset.univ.filter (fun c : C ↦ Boundary c ∧ coarse c = k), b c l
          else 0
    Nat.card {g : A → C //
      (∀ c, Fintype.card {a : A // g a = c} = n c) ∧
      (∀ a, coarse (g a) = (fine a).1) ∧
      ∀ c, Boundary c → ∀ l,
        Fintype.card {a : A // g a = c ∧ (fine a).2 = l} = b c l} =
      (∏ i, (Fintype.card {a : A // fine a = i}).factorial /
        ∏ di : {di : (C ⊕ K) × (K × L) // di.2 = i}, (m di.val).factorial) *
      (∏ d, (∑ i, m (d, i)).factorial /
        ∏ c : {c : C // collapse c = d}, (n c.val).factorial) := by
  exact MME.DWZUsefulWitnessCompatibility.compatible_assignment_card_of_witness
    fine coarse Boundary g0 hcoarse
