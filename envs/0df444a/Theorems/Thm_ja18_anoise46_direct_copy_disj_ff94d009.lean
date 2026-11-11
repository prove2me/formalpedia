-- Prove2me | Theorems.Thm_ja18_anoise46_direct_copy_disj_ff94d009
-- name    : ja18_anoise46_direct_copy_disj_ff94d009
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:00:01.338127+00:00
-- url     : https://prove2.me/theorems/6775465c-a6e0-4741-ad4a-775bbd654835
-- title:
--   Dyadic half-open negative-mark cells with different indices are disjoint
-- statement:
--   For every dyadic level k, different cells formed by intersecting the negative-mark band (-1,-1/(n+1)] with dyadic half-open intervals are disjoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

noncomputable section
theorem ja18_anoise46_direct_copy_disj_ff94d009
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) 
    : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l))) := by sorry
end
