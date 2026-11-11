-- Prove2me | Theorems.Thm_anoise46_direct_pointwise_upper_bound_f213822f
-- name    : anoise46_direct_pointwise_upper_bound_f213822f
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T14:55:54.676789+00:00
-- url     : https://prove2.me/theorems/3c82f391-d00a-4e15-a726-df93b4c33b06
-- title:
--   Anoise46 direct: Pointwise upper bound
-- statement:
--   At every point covered by the stated hypotheses, the left-hand expression is at most the right-hand expression.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

noncomputable section
theorem anoise46_direct_pointwise_upper_bound_f213822f
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) 
    (hDisj : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l))))
    (hUnique : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k : ℕ) (u : α) (hu : u ∈ F), ∃ i : ℕ, i < 2 ^ k ∧ j u ∈ C k i ∧
        ∀ l : ℕ, l < 2 ^ k → j u ∈ C k l → l = i)))
    (hCountAsSum : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k i : ℕ), ((F.filter (fun u => j u ∈ C k i)).card : ℝ) =
        ∑ u ∈ F, if j u ∈ C k i then (1 : ℝ) else 0)))
    (hReindex : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k : ℕ), q k =
      ∑ u ∈ F, ∑ i ∈ Finset.range (2 ^ k),
        if j u ∈ C k i then w k i else 0)))
    : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); (∀ (k : ℕ) (u : α) (hu : u ∈ F), |(∑ i ∈ Finset.range (2 ^ k),
          if j u ∈ C k i then w k i else 0) - j u| ≤
        (1 / 2 : ℝ) ^ k)) := by sorry
end
