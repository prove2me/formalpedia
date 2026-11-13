-- Prove2me | Theorems.Thm_thm_3_8_textbook
-- name    : thm_3_8_textbook
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:56:10.855682+00:00
-- url     : https://prove2.me/theorems/b91bcb50-624a-4300-a954-e53d71315204
-- title:
--   Chapter 3, thm_3_8: thm_3_8_textbook
-- statement:
--   Source theorem `thm_3_8_textbook` from Chapter 3, module `thm_3_8`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_8.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_8_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Tactic

open MeasureTheory Set ENNReal MeasurableSpace

theorem thm_3_8_textbook {Ω : Type*} [m : MeasurableSpace Ω] (F₀ : Set (Set Ω))
  (h_gen : m = MeasurableSpace.generateFrom F₀)
  (h_field_empty : ∅ ∈ F₀)
  (h_field_compl : ∀ s ∈ F₀, sᶜ ∈ F₀)
  (h_field_union : ∀ s ∈ F₀, ∀ t ∈ F₀, s ∪ t ∈ F₀)
  (μ1 μ2 : Measure Ω)
  (h_eq_on_F₀ : ∀ s ∈ F₀, μ1 s = μ2 s)
  (Ω_seq : ℕ → Set Ω)
  (h_disj : Pairwise (fun i j => Disjoint (Ω_seq i) (Ω_seq j)))
  (h_in_F₀ : ∀ i, Ω_seq i ∈ F₀)
  (h_univ : (⋃ i, Ω_seq i) = univ)
  (h_finite : ∀ i, μ1 (Ω_seq i) = μ2 (Ω_seq i) ∧ μ1 (Ω_seq i) < ⊤) :
  μ1 = μ2 := by sorry
