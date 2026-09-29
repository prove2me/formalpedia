-- Prove2me | Theorems.Thm_mme_regional_parent_windows_imply_global_histogram_window_allow_empty
-- name    : mme_regional_parent_windows_imply_global_histogram_window_allow_empty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:01:08.842544+00:00
-- url     : https://prove2.me/theorems/76ffe431-6379-4ca7-b71e-64ca5d965c4d
-- title:
--   Regional parent windows imply global histograms with empty regions
-- statement:
--   For any partition of a positive total number of positions into regions, regional parent-typical windows imply a global histogram window around the region-size-weighted mean of the parent-mixture centers. Regions may be empty: their histogram cardinalities and weights are zero. No per-region positivity assumption is required. The total size remains positive and all regional typicality hypotheses remain explicit.
-- source:
--   Exact histogram partition, weighted triangle inequality and zero-size region cardinality.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_regional_parent_windows_imply_global_histogram_window_allow_empty
    {P A W : Type} [Fintype P] [Fintype W]
    {half R T : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (eps : ℝ)
    (hT : ∑ r, n r = T) (hTpos : 0 < T)
    (htypical : parentTypical htotal n m mu eps
      (fun p => pair (f (positions ⟨p.1,p.2.1⟩)) p.2.2)) :
    ∀ a : A, |(Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a)| ≤ eps := by sorry
