-- Prove2me | Theorems.Thm_mme_regional_parent_count_structure
-- name    : mme_regional_parent_count_structure
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:47:37.848555+00:00
-- url     : https://prove2.me/theorems/fb4a3bf6-e35d-4f17-9fa8-aed4ee76b909
-- title:
--   The actual graded parent histogram has deterministic coarse grades
-- statement:
--   Derive both marginals and total mass of parentCounts from the literal physical words, and prove that a full joint parent word can occupy only one coarse grade. The sparsity property is proved from Graded.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_yz_hash_filter
import Mathlib
open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem mme_regional_parent_count_structure {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hg : Graded htotal i a f) : ∀ r,
    (∀ j, ∑ w, parentCounts (RecursiveXHash.block i a) f r j w =
      RecursiveThinSplit.count (RecursiveXHash.block i a r) j) ∧
    (∀ w, ∑ j, parentCounts (RecursiveXHash.block i a) f r j w =
      Fintype.card {t : Fin (n r) // ∀ h, f ⟨r,t,h⟩ = w h}) ∧
    (∑ j, ∑ w, parentCounts (RecursiveXHash.block i a) f r j w = n r) ∧
    (∀ w j k, parentCounts (RecursiveXHash.block i a) f r j w ≠ 0 →
      parentCounts (RecursiveXHash.block i a) f r k w ≠ 0 → j = k) := by sorry
