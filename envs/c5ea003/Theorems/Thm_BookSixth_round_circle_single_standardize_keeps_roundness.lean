-- Prove2me | Theorems.Thm_BookSixth_round_circle_single_standardize_keeps_roundness
-- name    : BookSixth.round_circle_single_standardize_keeps_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T18:37:39.355679+00:00
-- url     : https://prove2.me/theorems/f16104ab-5bc8-461c-be88-23b099b7c0f7
-- title:
--   Chapter 15: standardising one round circle keeps it round at every time
-- statement:
--   Let $D$ be a genuine round circle in $\mathbb{R}^3$. Then there is an ambient isotopy $K$ of $\mathbb{R}^3$ which starts at the identity, carries $D$ onto the standard circle `standardCircle k` at time $1$, and keeps $D$ a genuine round circle at every intermediate time. This strengthens the accepted existence statement `BookSixth.round_circle_single_standardize`, which records only the endpoint, to the roundness-at-every-time form needed by Chapter 15, Theorem 1. The reason the strengthening is available is that the accepted construction is a product of five families of similarities: a uniform rescaling by $\exp(-t \log r) > 0$, three rotations by $t\theta$, and a translation. A product of similarities is a similarity, and a similarity sends a round circle to a round circle, so every intermediate image is round. This is the one-circle instance of the general statement, where no pairwise-unlink or disjointness hypothesis is needed.
-- source:
--   Roundness-at-every-time form of the accepted theorem `BookSixth.round_circle_single_standardize` (theorem id 57b4c109-19d1-44b6-9291-0b9ef979db2c). That proof composes five isotopy families, `iso_affine_57b`, `iso_rot01_57b`, `iso_rot02_57b`, `iso_rot12_57b` and `iso_translate_57b`; their time maps are respectively a uniform rescaling by $\exp(-t \log r) > 0$, three rotations by $t\theta$ about the coordinate axes, and a translation, so each time map is a similarity with positive scale. Applying the proved `BookSixth.roundness_of_similarity_isotopy` (theorem id 10c3bc27-d678-476b-8828-7b90b6edc974) at each time gives the fifth conjunct. Needed as the base case of the Chapter 15, Theorem 1 motion, Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 130, https://doi.org/10.1007/978-3-662-57265-8_15.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_round_circle_single_standardize
import Theorems.Thm_BookSixth_roundness_of_similarity_isotopy
open BookSixth

theorem BookSixth.round_circle_single_standardize_keeps_roundness
    (D : Set Space3) (hroundD : RoundCircle D) (k : ℕ) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (K 1) '' D = standardCircle k ∧
      (∀ t, RoundCircle ((K t) '' D)) := by sorry
