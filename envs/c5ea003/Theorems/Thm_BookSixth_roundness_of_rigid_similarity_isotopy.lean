-- Prove2me | Theorems.Thm_BookSixth_roundness_of_rigid_similarity_isotopy
-- name    : BookSixth.roundness_of_rigid_similarity_isotopy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:42:50.009476+00:00
-- url     : https://prove2.me/theorems/7aa580d7-75a7-4bc5-894b-b3c71bbce246
-- title:
--   A family of scaled orthogonal maps keeps a round circle round at every time
-- statement:
--   Let C be a genuine round circle in R^3, and let G be a family of homeomorphisms of R^3 indexed by real time, with G equal to the identity at time zero. Suppose that at each time t the map G t is a positive scaling of an orthogonal linear map followed by a translation: there are a linear map A, a positive scale a, and a vector b such that A preserves the Euclidean inner product, a is strictly positive, and G t sends x to a*A(x) + b. Then the image of C under G t is a genuine round circle for every real time t, not merely at t = 1. This is the time-indexed form of the pointwise result BookSixth.euclidean_isometry_preserves_roundness, and it is the correct tool for the Chapter 15, Theorem 1 motion: the rigid motion that standardises a round circle is a composition of rotations, a positive scaling by an exponential, and a translation, so at each time it has exactly this form with a strictly positive scale. The hypothesis that a is positive is what makes the new radius a*r positive at every time, which is what no existing accepted lemma establishes.
-- source:
--   Support lemma for BookSixth.perfect_circles_pairwise_unlinked_motion (Chapter 15, Theorem 1 of Aigner-Ziegler, Proofs from THE BOOK, sixth edition).

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.roundness_of_rigid_similarity_isotopy {C : Set Space3}
    (hC : RoundCircle C) (G : ℝ → Space3 ≃ₜ Space3)
    (hG : ∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : Space3, 0 < a ∧
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (G t) x = a • (A x) + b)) :
    ∀ t, RoundCircle ((G t) '' C) := by sorry
