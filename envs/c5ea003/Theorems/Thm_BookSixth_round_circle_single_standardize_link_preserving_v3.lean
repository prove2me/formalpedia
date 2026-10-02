-- Prove2me | Theorems.Thm_BookSixth_round_circle_single_standardize_link_preserving_v3
-- name    : BookSixth.round_circle_single_standardize_link_preserving_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T06:43:14.434782+00:00
-- url     : https://prove2.me/theorems/1805d081-8665-48c0-bbc6-c8b3468e73bb
-- title:
--   Chapter 15 bridge: compatible link-preserving supported standardization
-- statement:
--   If a genuine round circle is pairwise unlinked with every earlier standard circle, then it can be carried to the next standard circle by a continuous ambient isotopy whose inverse is continuous and which fixes all earlier standard circles throughout the motion. The component order matches the unlink certificates transported by the prefix isotopy.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful supported one-circle transport child using the pairwise-unlink order needed by the prefix-transport certificate. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_single_standardize_link_preserving_v3 {n : ℕ}
    (D : Set Space3) (hroundD : RoundCircle D)
    (hpairs : ∀ i, i < n → IsUnlink (![standardCircle i, D] : Fin 2 → Set Space3)) :
    ∃ G : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x) ∧
      (G 1) '' D = standardCircle n ∧
      (∀ t i, i < n → (G t) '' standardCircle i = standardCircle i) := by sorry
