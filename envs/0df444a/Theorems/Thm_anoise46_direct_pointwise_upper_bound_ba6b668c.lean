-- Prove2me | Theorems.Thm_anoise46_direct_pointwise_upper_bound_ba6b668c
-- name    : anoise46_direct_pointwise_upper_bound_ba6b668c
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T14:55:49.5152+00:00
-- url     : https://prove2.me/theorems/eef21028-dd4c-4189-bfaa-10546617fa75
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
theorem anoise46_direct_pointwise_upper_bound_ba6b668c
    {α : Type*} [DecidableEq α] (n : ℕ) (F : Finset α)
    (j : α → ℝ)
    (hF : ∀ u ∈ F, j u ∈ Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))) 
    (hDisj : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); let I : ℝ := ∑ u ∈ F, j u; let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ); (∀ (k i l : ℕ) (hil : i ≠ l), Disjoint (C k i) (C k l))))
    (hUnique : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); let I : ℝ := ∑ u ∈ F, j u; let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ); (∀ (k : ℕ) (u : α) (hu : u ∈ F), ∃ i : ℕ, i < 2 ^ k ∧ j u ∈ C k i ∧
        ∀ l : ℕ, l < 2 ^ k → j u ∈ C k l → l = i)))
    (hCountAsSum : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); let I : ℝ := ∑ u ∈ F, j u; let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ); (∀ (k i : ℕ), ((F.filter (fun u => j u ∈ C k i)).card : ℝ) =
        ∑ u ∈ F, if j u ∈ C k i then (1 : ℝ) else 0)))
    (hReindex : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); let I : ℝ := ∑ u ∈ F, j u; let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ); (∀ (k : ℕ), q k =
      ∑ u ∈ F, ∑ i ∈ Finset.range (2 ^ k),
        if j u ∈ C k i then w k i else 0)))
    (hInner : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); let I : ℝ := ∑ u ∈ F, j u; let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ); (∀ (k : ℕ) (u : α) (hu : u ∈ F), |(∑ i ∈ Finset.range (2 ^ k),
          if j u ∈ C k i then w k i else 0) - j u| ≤
        (1 / 2 : ℝ) ^ k)))
    : (let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))); let C : ℕ → ℕ → Set ℝ := (fun k i => B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k) (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)); let w : ℕ → ℕ → ℝ := fun k i => -1 + (i : ℝ) / (2 : ℝ) ^ k; let q : ℕ → ℝ := (fun k => ∑ i ∈ Finset.range (2 ^ k), w k i * ((F.filter (fun u => j u ∈ C k i)).card : ℝ)); let I : ℝ := ∑ u ∈ F, j u; let e : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k * (F.card : ℝ); (∀ (k : ℕ), |q k - I| ≤ e k)) := by sorry
end
