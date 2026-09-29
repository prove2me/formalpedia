-- Prove2me | Theorems.Thm_mme_regional_target_marginals
-- name    : mme_regional_target_marginals
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T20:48:10.513905+00:00
-- url     : https://prove2.me/theorems/af601d76-0502-4340-a1f3-3a4a5ae0b94f
-- title:
--   Target blocks are exactly all words with the prescribed mode counts
-- statement:
--   Starting from any actual target address, derive both joint and mode masses and construct a target lift of every prescribed coarse-mode word by matching position permutations.
-- source:
--   Uniform regional entropy estimates for the actual integer CW construction in the More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Supporting result; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_regional_split_entropy_data
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem mme_regional_target_marginals {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3)
    (a : Address half R parent n) (ha : a ∈ target m) :
    (∀ r, ∑ c, m r c = n r) ∧
    (∀ r, ∑ j, marginalCounts m i r j = n r) ∧
    ((target (n := n) m).image (block i) =
      Finset.univ.filter (fun y : ∀ r, Fin (n r) → Fin (half + 1) ↦
        ∀ r j, count (y r) j = marginalCounts m i r j)) := by sorry
