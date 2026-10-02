-- Prove2me | Theorems.Thm_BookSixth_pairwise_disjoint_cutoffs_lipschitz
-- name    : BookSixth.pairwise_disjoint_cutoffs_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T21:16:10.358464+00:00
-- url     : https://prove2.me/theorems/74e478ce-a898-43c5-9490-e6bcaadc0a48
-- title:
--   A finite family of pairwise disjoint compact sets admits Lipschitz cut-offs that are one on one set and zero on all the others
-- statement:
--   Let S_0, ..., S_{n-1} be pairwise disjoint compact subsets of three-dimensional real space. There is a positive real number eps and, for each i, a function chi_i from space to the reals with the following properties.
--
--     1. eps is strictly positive and the same for every i.
--     2. Each chi_i is Lipschitz with the single constant 1/eps. The constant is finite but is NOT required to be less than one, and that is essential: chi_i equals one on a whole neighbourhood of S_i, so no useful hypothesis could force its Lipschitz constant below one.
--     3. chi_i equals exactly one everywhere on S_i.
--     4. chi_i equals exactly zero everywhere on S_j for every j different from i.
--
--   The separation step is what makes the constant uniform: pairwise disjointness, together with compactness, gives a positive gap between each pair, and the minimum of the finitely many gaps is a single eps that works simultaneously for every pair. The witnesses are chi_i x = min 1 (max 0 (1 - dist(x, S_i) / eps)), the same distance-based cut-off as in the single-set case, with the distance now measured to the whole compact set.
--
--   This is the localisation input for building an ambient isotopy out of a family of independent component motions. Given maps S_{i,t} close to the identity, the patched map F_t x = x + sum_i chi_i x * (S_{i,t} x - x) then satisfies (F_t) '' S_i = S_{i,t} '' S_i exactly, because on S_i all cut-offs vanish except chi_i, which is one. The ambient map may be badly behaved away from the sets; that does not matter, because agreement on the set itself is all that is needed for the image of that set to retain its shape.
-- source:
--   Chapter 15 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The separation step is Disjoint.exists_thickenings (Mathlib/Topology/MetricSpace/Thickening.lean:418), which gives, for disjoint compact (respectively closed) sets, a positive delta with the corresponding thickenings disjoint; taking the minimum over the finitely many pairs makes the delta uniform. The cut-off uses Metric.lipschitz_infDist_pt (Mathlib/Topology/MetricSpace/HausdorffDistance.lean:664) together with LipschitzWith.min and LipschitzWith.max (Mathlib/Topology/MetricSpace/Lipschitz.lean:186 and :182). For the mission this is the localisation step for BookSixth.bump_perturbation_is_homeomorph_v3 (2691f203), Proved, and the disjoint neighbourhoods it needs are supplied by BookSixth.pairwise_disjoint_open_neighbourhoods (7fd98b02), Proved. Exact agreement on the set then gives roundness through BookSixth.patch_agrees_with_its_own_similarity (ac9094b3), Proved, and BookSixth.localized_similarity_isotopy_keeps_roundness (f90b81d4), Proved.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.pairwise_disjoint_cutoffs_lipschitz {n : ℕ} (S : Fin n → Set Space3)
    (hS : ∀ i, IsCompact (S i)) (hD : ∀ i j, i ≠ j → Disjoint (S i) (S j)) :
    ∃ (eps : ℝ) (chi : Fin n → Space3 → ℝ), 0 < eps ∧
      (∀ i, LipschitzWith (Real.toNNReal (1 / eps)) (chi i)) ∧
      (∀ i x, x ∈ S i → chi i x = 1) ∧
      (∀ i j, i ≠ j → ∀ x, x ∈ S j → chi i x = 0) := by sorry
