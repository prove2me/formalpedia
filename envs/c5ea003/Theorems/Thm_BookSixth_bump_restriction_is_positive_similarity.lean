-- Prove2me | Theorems.Thm_BookSixth_bump_restriction_is_positive_similarity
-- name    : BookSixth.bump_restriction_is_positive_similarity
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T06:42:59.347651+00:00
-- url     : https://prove2.me/theorems/b1eac2a1-faff-4ade-aa0f-90a64aa619d6
-- title:
--   On the support of its own component, the cut-off patched map equals that component's positive similarity
-- statement:
--   This is a thin packaging lemma, not a new geometric fact. The cut-off patched ambient map has value x + sum over j of chi j x times (S j x - x) at the point x. On a point x lying in the component C i, the cut-off of that component is one and every other cut-off vanishes, so the accepted identity BookSixth.patch_agrees_with_its_own_similarity collapses the whole sum to its i-th term, leaving S i x. When each local motion S i is itself a positive similarity x maps to a i times A i x plus b i, this says that the patched ambient map restricts, on the support of its own component, to exactly that component's positive similarity.
--
--   The restriction to x in C i is essential and is what makes the statement non-vacuous. Asserting the corresponding equality for all x, without the membership hypothesis, would be true but trivial, since the two finite sums are then equal term by term with no use of the cut-off properties at all. Here the content is that the single global patched expression, which mixes all components together through the sum, provably reduces on each component to that component's own similarity. That is the identification needed to pass from the cut-off patching description of the ambient isotopy to the per-component similarity description consumed by BookSixth.localized_similarity_isotopy_keeps_roundness (f90b81d4-2047-4b46-b7f7-15dc7f938dac), which then concludes that every intermediate image of every component remains a genuine round circle.
--
--   Two details of the target lemma are load-bearing and are mirrored exactly rather than paraphrased. The linear map is a continuous linear map (Fin 3 -> R) ->L[R] (Fin 3 -> R) and not a bare function, because the ambient motion is a homeomorphism of a topological space and the similarity factor must be realised continuously. The isometry condition there is stated on the Euclidean bilinear form, the sum over k of (A x) k times (A y) k, and not on the supremum norm carried by Space3 = Fin 3 -> R, for which forall x, norm (A x) = norm x is a different and weaker condition. The positive scalar requirement a i > 0 is likewise part of that hypothesis and is what makes the map a similarity rather than a general affine map.
-- source:
--   Chapter 15 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15. This child isolates the identification between two already-accepted theorems and introduces no new geometry. The accepted identity BookSixth.patch_agrees_with_its_own_similarity (ac9094b3-ea63-4895-8a85-0814b5dd0cb4) collapses the cut-off sum to the i-th term on the support of component i, using Finset.sum_eq_single together with the additive group laws of Space3 = Fin 3 -> R. The accepted theorem BookSixth.localized_similarity_isotopy_keeps_roundness (f90b81d4-2047-4b46-b7f7-15dc7f938dac) consumes the per-component positive-similarity description and concludes that every intermediate image of every component is a genuine round circle. This child supplies precisely the passage from the first description to the second, so that the roundness lemma applies to the cut-off patched isotopy.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.bump_restriction_is_positive_similarity {n : ℕ}
    (C : Fin n → Set Space3) (chi : Fin n → Space3 → ℝ) (S : Fin n → Space3 → Space3)
    (A : Fin n → (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)) (a : Fin n → ℝ) (b : Fin n → Fin 3 → ℝ)
    (hone : ∀ i x, x ∈ C i → chi i x = 1)
    (hzero : ∀ i j x, i ≠ j → x ∈ C i → chi j x = 0)
    (hS : ∀ i x, S i x = a i • (A i x) + b i) :
    ∀ (i : Fin n) (x : Space3), x ∈ C i →
      x + ∑ j, chi j x • (S j x - x) = a i • (A i x) + b i := by sorry
