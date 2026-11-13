-- Prove2me | Theorems.Thm_thm_3_5
-- name    : thm_3_5
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:43:07.914552+00:00
-- url     : https://prove2.me/theorems/d9f7956b-697c-41a4-8ecb-b1acac6b69c0
-- title:
--   Chapter 3, thm_3_5: thm_3_5
-- statement:
--   Source theorem `thm_3_5` from Chapter 3, module `thm_3_5`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_5.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_8_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set ENNReal

theorem thm_3_5 {α : Type*} (s : Set (Set α)) (μ : Set α → ℝ≥0∞)
    (h_empty_val : μ ∅ = 0)
    (h_field_empty : ∅ ∈ s)
    (h_field_compl : ∀ A ∈ s, Aᶜ ∈ s)
    (h_field_union : ∀ A ∈ s, ∀ B ∈ s, A ∪ B ∈ s)
    (h_fin_add : ∀ A ∈ s, ∀ B ∈ s, Disjoint A B → μ (A ∪ B) = μ A + μ B)
    (h_sigma_subadd : ∀ f : ℕ → Set α, (∀ i, f i ∈ s) → (⋃ i, f i) ∈ s →
      μ (⋃ i, f i) ≤ ∑' i, μ (f i)) :
    ∀ f : ℕ → Set α, (∀ i, f i ∈ s) → (∀ i j, i ≠ j → Disjoint (f i) (f j)) →
      (⋃ i, f i) ∈ s → μ (⋃ i, f i) = ∑' i, μ (f i) := by sorry
