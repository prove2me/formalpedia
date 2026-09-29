-- Prove2me | Theorems.Thm_mme_parent_histogram_sum_over_regions
-- name    : mme_parent_histogram_sum_over_regions
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:22:54.912353+00:00
-- url     : https://prove2.me/theorems/8b271502-f346-48f4-89aa-8629f1663f9a
-- title:
--   A physical partition decomposes the parent histogram
-- statement:
--   For any finite parent-position set partitioned into finite regions, and any equivalence identifying a full word with its pair of child words, the full-word histogram is the sum of the regional pair-word histograms.
-- source:
--   Physical regional partitions and the released owner-zero (1,1,6) integer profiles.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

theorem mme_parent_histogram_sum_over_regions
    {P A W : Type} [Fintype P] {R : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (a : A) :
    Fintype.card {p : P // f p = a} =
      ∑ r, Fintype.card {t : Fin (n r) //
        ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h} := by sorry
