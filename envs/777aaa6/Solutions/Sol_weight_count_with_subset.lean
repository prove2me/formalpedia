-- Prove2me | solution 1 for weight_count_with_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-05-09T02:11:37.575042+00:00
-- url     : https://prove2.me/submissions/0a461808-4d04-4975-8168-5240d9c512e0

import Theorems.Thm_weight_count_with_subset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Nat.Choose.Basic

/-!
# Proof — `weight_count_with_subset`

Two-step bijection:
  `{y : Fin b → Bool, weight y = t, S ⊆ trueSet y}`
    ↦ `{T : Finset (Fin b), T.card = t, S ⊆ T}`        (y ↦ trueSet y)
    ↦ `(univ \ S).powersetCard (t - |S|)`              (T ↦ T \ S, when |S| ≤ t)

The last set has cardinality `(b - |S|).choose (t - |S|)` directly via
`Finset.card_powersetCard`. When `|S| > t`, no `t`-element subset can
contain `S`, so the count is `0`.
-/

namespace WeightCountWithSubset

variable {b : ℕ}

/-- Step 1: bijection `y ↦ trueSet y` between weight-`t` Booleans containing `S`
    and `t`-element subsets of `Fin b` containing `S`. -/
lemma card_bool_eq_card_subsets (S : Finset (Fin b)) (t : ℕ) :
    ((Finset.univ : Finset (Fin b → Bool)).filter
        (fun y => ((Finset.univ : Finset (Fin b)).filter (fun i => y i = true)).card = t
                    ∧ S ⊆ (Finset.univ : Finset (Fin b)).filter (fun i => y i = true))).card
      = (((Finset.univ : Finset (Fin b)).powersetCard t).filter (S ⊆ ·)).card := by
  classical
  apply Finset.card_bij
    (fun (y : Fin b → Bool) (_ : y ∈ _) =>
        (Finset.univ : Finset (Fin b)).filter (fun i => y i = true))
  · intros y hy
    rw [Finset.mem_filter] at hy
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.filter_subset _ _, hy.2.1⟩, hy.2.2⟩
  · intros y₁ hy₁ y₂ hy₂ heq
    funext i
    have hiff : (i ∈ (Finset.univ : Finset (Fin b)).filter (fun k => y₁ k = true)) ↔
                (i ∈ (Finset.univ : Finset (Fin b)).filter (fun k => y₂ k = true)) := by
      rw [heq]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiff
    cases h₁ : y₁ i <;> cases h₂ : y₂ i
    · rfl
    · simp [h₁, h₂] at hiff
    · simp [h₁, h₂] at hiff
    · rfl
  · intros T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    refine ⟨fun i => decide (i ∈ T), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · have hfilt : (Finset.univ : Finset (Fin b)).filter
                        (fun i => (decide (i ∈ T) : Bool) = true) = T := by
          ext i; simp
        rw [hfilt]; exact hT.1.2
      · intro i hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have : i ∈ T := hT.2 hi
        simp [this]
    · ext i
      simp

/-- Step 2: bijection `T ↦ T \ S` between `t`-subsets containing `S` and
    `(t - |S|)`-subsets of `univ \ S`, when `|S| ≤ t`. -/
lemma card_subsets_eq_choose (S : Finset (Fin b)) (t : ℕ) (hk : S.card ≤ t) :
    (((Finset.univ : Finset (Fin b)).powersetCard t).filter (S ⊆ ·)).card
      = (b - S.card).choose (t - S.card) := by
  classical
  rw [show (b - S.card).choose (t - S.card)
        = (((Finset.univ : Finset (Fin b)) \ S).powersetCard (t - S.card)).card by
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]]
  apply Finset.card_bij
    (fun (T : Finset (Fin b)) (_ : T ∈ _) => T \ S)
  · intros T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro i hi
      rw [Finset.mem_sdiff] at hi
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ i, hi.2⟩
    · rw [Finset.card_sdiff_of_subset hT.2, hT.1.2]
  · intros T₁ hT₁ T₂ hT₂ heq
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT₁ hT₂
    -- Recover T_i = (T_i \ S) ∪ S since S ⊆ T_i
    have h1 : T₁ = T₁ \ S ∪ S := (Finset.sdiff_union_of_subset hT₁.2).symm
    have h2 : T₂ = T₂ \ S ∪ S := (Finset.sdiff_union_of_subset hT₂.2).symm
    rw [h1, h2, heq]
  · intros T' hT'
    rw [Finset.mem_powersetCard] at hT'
    -- Inverse: T := T' ∪ S
    refine ⟨T' ∪ S, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.subset_union_right⟩
      have h_disj : Disjoint T' S := by
        rw [Finset.disjoint_right]
        intros x hx hxT'
        have := hT'.1 hxT'
        rw [Finset.mem_sdiff] at this
        exact this.2 hx
      rw [Finset.card_union_of_disjoint h_disj, hT'.2]
      omega
    · -- (T' ∪ S) \ S = T' since T' ∩ S = ∅
      rw [Finset.union_sdiff_right]
      rw [Finset.sdiff_eq_self_iff_disjoint.mpr]
      rw [Finset.disjoint_right]
      intros x hx hxT'
      have := hT'.1 hxT'
      rw [Finset.mem_sdiff] at this
      exact this.2 hx

end WeightCountWithSubset

open WeightCountWithSubset

theorem solution
    {b : ℕ} (S : Finset (Fin b)) (t : ℕ) :
    ((Finset.univ : Finset (Fin b → Bool)).filter
        (fun y => ((Finset.univ : Finset (Fin b)).filter (fun i => y i = true)).card = t
                    ∧ S ⊆ (Finset.univ : Finset (Fin b)).filter (fun i => y i = true))).card
      = if S.card ≤ t then (b - S.card).choose (t - S.card) else 0 := by
  classical
  rw [card_bool_eq_card_subsets]
  by_cases hk : S.card ≤ t
  · rw [if_pos hk, card_subsets_eq_choose S t hk]
  · rw [if_neg hk]
    push_neg at hk
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intros T hT
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hT
    have h1 : S.card ≤ T.card := Finset.card_le_card hT.2
    omega
