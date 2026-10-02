-- Prove2me | Theorems.Thm_BookSixth_standardizing_time_maps_are_similarities
-- name    : BookSixth.standardizing_time_maps_are_similarities
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T00:11:53.645311+00:00
-- url     : https://prove2.me/theorems/70d16099-287a-4360-bf09-e01ddf38bc25
-- title:
--   Chapter 15: the standardising isotopy is a positive similarity at every time
-- statement:
--   Let $D$ be a genuine round circle in $\mathbb{R}^3$. Then the ambient isotopy which starts at the identity and carries $D$ onto the standard circle `standardCircle k` can be chosen so that at every time $t$ its map is a positive scaling composed with an inner-product-preserving linear map and a translation: $H_t(x) = a_t A_t x + b_t$ with $a_t > 0$. The reason is structural and is inherited from the accepted construction of `BookSixth.round_circle_single_standardize`, whose isotopy is the composite of five families: a uniform rescaling by $\exp(-t \log r) > 0$, three rotations by $t\theta$ about the coordinate axes, and a translation. A uniform rescaling is a positive similarity, each coordinate-plane rotation is inner-product preserving, and both classes are closed under composition, so the composite has the stated form at every time. This is what makes the roundness-at-every-time form of Chapter 15, Theorem 1 available: it is exactly the hypothesis of the accepted `BookSixth.roundness_of_rigid_similarity_isotopy`. The weaker statement that each time map is a uniform scalar `a x + b` is FALSE, and the platform has accepted a disproof of it, because a product of rotations about different axes is a general orthogonal map rather than a scalar multiple; the orthogonal factor is therefore essential.
-- source:
--   Pointwise strengthening of the accepted theorem `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c), whose accepted proof composes `iso_affine_57b`, `iso_rot01_57b`, `iso_rot02_57b`, `iso_rot12_57b` and `iso_translate_57b`. Those helpers are private to that proof file and are not importable, so they are restated here with pointwise time maps. Each coordinate-plane rotation preserves the Euclidean bilinear form `sum i, x i * y i`, by `Real.cos_sq_add_sin_sq`; the rescaling factor `exp(-(t * log r))` is positive for every real `t` when `r > 0`; and both classes are closed under composition. Needed to obtain the roundness-at-every-time statement of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15, by combining with the accepted `BookSixth.roundness_of_rigid_similarity_isotopy` (theorem id 7aa580d7-75a7-4bc5-894b-b3c71bbce246). Supersedes the disproved `BookSixth.single_standardize_pointwise` (89f85f15-4388-47ea-8e29-4b570e94efe9).

import Mathlib
import Definitions.Def_BookSixth
open BookSixth

theorem BookSixth.standardizing_time_maps_are_similarities
    (D : Set Space3) (hroundD : RoundCircle D) (k : ℕ) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (H 1) '' D = standardCircle k ∧
      (∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ a : ℝ, ∃ b : (Fin 3 → ℝ), 0 < a ∧
        (∀ x y : (Fin 3 → ℝ), (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : (Fin 3 → ℝ), H t x = a • (A x) + b)) := by sorry
