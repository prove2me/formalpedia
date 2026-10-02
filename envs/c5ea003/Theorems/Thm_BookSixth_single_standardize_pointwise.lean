-- Prove2me | Theorems.Thm_BookSixth_single_standardize_pointwise
-- name    : BookSixth.single_standardize_pointwise
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-25T18:47:06.638713+00:00
-- url     : https://prove2.me/theorems/89f85f15-4388-47ea-8e29-4b570e94efe9
-- title:
--   Chapter 15: the standardising isotopy is a positive similarity at every time
-- statement:
--   Let $D$ be a genuine round circle in $\mathbb{R}^3$. Then the ambient isotopy $K$ of the accepted theorem `BookSixth.round_circle_single_standardize`, which starts at the identity and carries $D$ onto the standard circle `standardCircle k`, is at every time $t$ a similarity of positive scale: there are a real number $a_t > 0$ and a vector $b_t$ with $K_t(x) = a_t x + b_t$ for all $x$. This is the pointwise description of the time maps that the accepted theorem does not record, and it is what makes the roundness-at-every-time form available. The reason is structural: the accepted construction composes five families, a uniform rescaling by $\exp(-t\log r) > 0$, three rotations by $t\theta$ about the coordinate axes, and a translation, and a product of similarities is a similarity with positive scale.
-- source:
--   Pointwise strengthening of the accepted theorem `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c). That theorem records only the time-1 formula `(H 1) x = r⁻¹ • (x - c)` after the rotations and translation; its construction composes `iso_affine_57b`, `iso_rot01_57b`, `iso_rot02_57b`, `iso_rot12_57b` and `iso_translate_57b`, whose time maps are respectively a uniform rescaling by $\exp(-t \log r) > 0$, three rotations by $t\theta$ about the coordinate axes, and a translation, so each is a similarity with positive scale and a product of similarities is such a similarity. Needed to obtain the roundness-at-every-time statement required by Chapter 15, Theorem 1 of Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), p. 130, https://doi.org/10.1007/978-3-662-57265-8_15, by combining with `BookSixth.roundness_of_similarity_isotopy` (theorem id 10c3bc27-d678-476b-8828-7b90b6edc974).

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_round_circle_single_standardize
open BookSixth

theorem BookSixth.single_standardize_pointwise (D : Set Space3) (k : ℕ)
    (hroundD : RoundCircle D) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle k ∧
      (∀ t, ∃ q : ℝ × Space3, 0 < q.1 ∧
        (∀ x : Space3, (K t) x = (q.1 • x) + q.2)) := by sorry
