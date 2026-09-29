-- Prove2me | Theorems.Thm_mme_parent_typical_of_global_histogram_window
-- name    : mme_parent_typical_of_global_histogram_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T12:50:48.865854+00:00
-- url     : https://prove2.me/theorems/c8d7c4c2-f86c-4e88-8f1d-f805bfaf1142
-- title:
--   Regional parent windows from globally normalized histograms
-- statement:
--   Let a finite family of full words be partitioned into cells. In each chosen region $r$, enumerate its cell by $n_r>0$ positions, and identify a full word bijectively with its ordered pair of child words. Let $H(c,a)$ be the exact full-word histogram and $\beta(c,a)$ its globally normalized center. Suppose, for a positive total $T$,
--   \[
--   \left|H(c_r,a)/T-\beta(c_r,a)\right|\le\delta.
--   \]
--   Assume that the prescribed regional parent mixture satisfies
--   \[
--   \operatorname{mixture}_r(w)=\frac{T}{n_r}\,\beta(c_r,\operatorname{pair}^{-1}(w)),
--   \qquad \frac{T\delta}{n_r}<\varepsilon.
--   \]
--   Then the physical two-half words obtained from the cell enumeration are parent-typical with tolerance $\varepsilon$ in every region. The bound retains the exact conversion between global and regional frequency normalizations.
-- source:
--   Exact physical cell histograms and global-to-regional frequency normalization.

import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_recursive_yz_cell_partition
import Mathlib.Algebra.Order.Field.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

theorem mme_parent_typical_of_global_histogram_window
    {P C A W : Type} [Fintype P] [Fintype W]
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (cell : P → C) (f : P → A) (region : Fin R → C)
    (fiber : ∀ r, Fin (n r) ≃ {p : P // cell p = region r})
    (pair : A ≃ (Fin 2 → W)) (center : C → A → ℝ)
    (total delta eps : ℝ) (htotal_pos : 0 < total) (hn : ∀ r, 0 < n r)
    (hwindow : ∀ r a, |(count cell f (region r) a : ℝ) / total -
      center (region r) a| ≤ delta)
    (hmixture : ∀ r w, parentMixture htotal n m mu r w =
      total / (n r : ℝ) * center (region r) (pair.symm w))
    (htolerance : ∀ r, total / (n r : ℝ) * delta < eps) :
    parentTypical htotal n m mu eps
      (fun p ↦ pair (f (fiber p.1 p.2.1).val) p.2.2) := by sorry
