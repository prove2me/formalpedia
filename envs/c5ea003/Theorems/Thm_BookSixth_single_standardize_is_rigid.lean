-- Prove2me | Theorems.Thm_BookSixth_single_standardize_is_rigid
-- name    : BookSixth.single_standardize_is_rigid
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-25T18:48:45.443008+00:00
-- url     : https://prove2.me/theorems/102633b6-c1bd-4846-b175-844ae9c25dee
-- title:
--   Chapter 15: the standardising isotopy is a rigid motion at every time
-- statement:
--   Let $D$ be a genuine round circle in $\mathbb{R}^3$. Then the ambient isotopy of the accepted theorem `BookSixth.round_circle_single_standardize`, which starts at the identity and carries $D$ onto the standard circle `standardCircle k`, is at every time $t$ a rigid motion of $\mathbb{R}^3$: there is a linear map $A_t$ preserving the Euclidean inner product and a vector $b_t$ with $K_t(x) = A_t x + b_t$ for all $x$. This is the pointwise description of the time maps, which the accepted theorem does not record. The reason is structural: the accepted construction composes five families, a uniform rescaling by $\exp(-t\log r) > 0$, three rotations by $t\theta$ about the coordinate axes, and a translation. A rescaling composed with a rotation is a rotation followed by a rescaling, and a product of inner-product-preserving maps preserves the inner product, so the composite is rigid. This is the statement that yields the roundness-at-every-time form of Chapter 15, Theorem 1, by combining with `BookSixth.roundness_of_rigid_isotopy`. The weaker-looking version of this statement that asks each time map to be a uniform scalar times the identity plus a translation is false, because a product of rotations about different axes is a general orthogonal map rather than a scalar multiple.
-- source:
--   Pointwise strengthening of the accepted theorem `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c). That theorem records only the time-1 formula; its accepted proof composes `iso_affine_57b`, `iso_rot01_57b`, `iso_rot02_57b`, `iso_rot12_57b` and `iso_translate_57b`, whose time maps are respectively a uniform rescaling by $\exp(-t \log r) > 0$, three rotations by $t\theta$ about the coordinate axes, and a translation. Each preserves the Euclidean bilinear form, and so does any product of them, which is why the conclusion is stated with an inner-product-preserving linear map rather than a scalar. Needed to obtain the roundness-at-every-time statement of Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15, by combining with the proved `BookSixth.roundness_of_rigid_isotopy` (theorem id fafe1771-4766-4182-8a79-4768ebb79cf6). This supersedes the incorrect draft `BookSixth.single_standardize_pointwise` (89f85f15-4388-47ea-8e29-4b570e94efe9), whose conclusion required each time map to be a uniform scalar multiple of the identity, which is false for a product of rotations about different axes.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_round_circle_single_standardize
open BookSixth

theorem BookSixth.single_standardize_is_rigid (D : Set Space3) (k : ℕ)
    (hroundD : RoundCircle D) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle k ∧
      (∀ t, ∃ A : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ), ∃ q : ℝ × Space3,
        (∀ x y : Space3, (∑ i, (A x) i * (A y) i) = ∑ i, x i * y i) ∧
        (∀ x : Space3, (K t) x = (A x) + q.2)) := by sorry
