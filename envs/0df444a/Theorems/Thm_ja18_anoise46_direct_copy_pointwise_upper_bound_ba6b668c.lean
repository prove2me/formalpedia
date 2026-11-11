-- Prove2me | Theorems.Thm_ja18_anoise46_direct_copy_pointwise_upper_bound_ba6b668c
-- name    : ja18_anoise46_direct_copy_pointwise_upper_bound_ba6b668c
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:59:52.857193+00:00
-- url     : https://prove2.me/theorems/68fef6de-0f13-420f-b677-3baa1dad2155
-- title:
--   Finite marked dyadic weighted sum has cardinality-times-mesh error
-- statement:
--   Given finite mark reindexing and individual coefficient errors, the absolute difference between the cell-weighted total and signed mark sum is at most 2^-k times the number of marks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_anoise34_dyadic_mark_cell_endpoint_error
import Theorems.Thm_AvramDividend_Classical_avram_anoise43_unit_dyadic_halfopen_cover
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology

noncomputable section
theorem ja18_anoise46_direct_copy_pointwise_upper_bound_ba6b668c
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
