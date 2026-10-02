-- Prove2me | Theorems.Thm_BookSixth_localized_similarity_isotopy_keeps_roundness
-- name    : BookSixth.localized_similarity_isotopy_keeps_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-27T20:23:25.93638+00:00
-- url     : https://prove2.me/theorems/f90b81d4-2047-4b46-b7f7-15dc7f938dac
-- title:
--   An ambient isotopy that agrees with a similarity on each component keeps every component round at every time
-- statement:
--   Localised roundness under a componentwise-similarity ambient isotopy. Let C_0, ..., C_{m-1} be round circles in R^3 and let K : R -> Homeo(R^3) be an ambient isotopy. Suppose that for every time t and every index i there exist a positive scale a, an inner-product preserving linear map A and a translation b such that the ambient map K_t agrees ON THE COMPONENT C_i with the similarity x -> a A x + b. Then at every time t every image (K_t) '' C_i is again a round circle.
--
--   The agreement is required only on the component C_i, not on all of space, and the witness (A, a, b) may depend on both t and i. This locality is essential: a single global similarity per time is satisfiable for one circle but is uninhabitable for a family of two or more circles with unequal radii, because a similarity scales all radii by the same factor whereas the standard circles all have radius exactly 1.
--
--   This is NOT the same as the single-circle theorem BookSixth.standardizing_time_maps_are_similarities (70d16099), which is also Proved; that theorem's stronger hypothesis, that K_t is a single global similarity at every time, is what fails for a family. This theorem is the correct family-sized replacement.
-- source:
--   Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. The definitions (Space3, RoundCircle) are from the definition module Definitions.Def_BookSixth. The conclusion is BookSixth.euclidean_isometry_preserves_roundness (837c17d9), whose binder order is exactly (C) (A) (b) (a) (hA) (ha) (hC); the agreement hypothesis is transported through the set image by Set.image_congr. The single-circle global version is BookSixth.standardizing_time_maps_are_similarities (70d16099) and the family-sized rigid form is BookSixth.roundness_of_rigid_similarity_isotopy (7aa580d7).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.localized_similarity_isotopy_keeps_roundness {m : ℕ}
    (C : Fin m → Set Space3) (K : ℝ → Space3 ≃ₜ Space3)
    (hround : ∀ i, RoundCircle (C i))
    (hom : ∀ t i, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3,
      0 < a ∧ (∀ x y : Space3, (∑ k, (A x) k * (A y) k) = ∑ k, x k * y k) ∧
      ∀ x ∈ C i, K t x = a • (A x) + b) :
    ∀ t i, RoundCircle ((K t) '' C i) := by sorry
