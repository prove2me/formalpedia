-- Prove2me | Theorems.Thm_BookSixth_roundness_of_similarity_isotopy
-- name    : BookSixth.roundness_of_similarity_isotopy
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T17:52:12.705324+00:00
-- url     : https://prove2.me/theorems/10c3bc27-d678-476b-8828-7b90b6edc974
-- title:
--   Chapter 15 primitive: a similarity isotopy keeps every image round
-- statement:
--   Let $C$ be a genuine round circle and let $G$ be a family of homeomorphisms of $\mathbb{R}^3$. Suppose that for every time $t$ the map $G_t$ is a similarity of positive scale, that is $G_t(x) = a_t x + b_t$ with $a_t > 0$. Then every intermediate image $G_t(C)$ is again a genuine round circle. This is the pointwise time-version of `BookSixth.similarity_preserves_roundness` and is the composition rule used to build a motion that keeps every image round.
-- source:
--   Immediate composition of the proved theorem `BookSixth.similarity_preserves_roundness` (theorem id 050cc58c-fca3-4342-912b-c3ad3825e5ec), applied at each time and with the pointwise hypothesis turned into an image equality by `Set.image_congr`. Used in the roundness-preserving ambient motion of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15.

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.roundness_of_similarity_isotopy {C : Set Space3}
    (hC : RoundCircle C) (G : ℝ → Space3 ≃ₜ Space3)
    (hsim : ∀ t, ∃ q : ℝ × Space3, 0 < q.1 ∧
        (∀ x : Space3, (G t) x = (q.1 • x) + q.2)) :
    ∀ t, RoundCircle ((G t) '' C) := by sorry
