-- Prove2me | Theorems.Thm_anoise46_direct_disj_ff94d009
-- name    : anoise46_direct_disj_ff94d009
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T14:55:32.404948+00:00
-- url     : https://prove2.me/theorems/691394a6-789d-4277-ac16-2a08773ec9a6
-- title:
--   Anoise46 direct: Auxiliary result
-- statement:
--   Under the explicitly listed hypotheses, the assertion in the formal Lean theorem statement holds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

noncomputable section
theorem anoise46_direct_disj_ff94d009
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) 
    : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l))) := by sorry
end
