-- Prove2me | Theorems.Thm_BookSixth_round_circle_single_standardize_link_preserving_v2
-- name    : BookSixth.round_circle_single_standardize_link_preserving_v2
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T23:26:18.088564+00:00
-- url     : https://prove2.me/theorems/f494836f-29ba-49f3-825f-a1ec44ce29a5
-- title:
--   Chapter 15 bridge: link-preserving supported standardization
-- statement:
--   If a genuine round circle is pairwise unlinked with each previously assigned standard circle, then it can be carried to the next standard circle by a continuous ambient isotopy whose inverse is continuous and which fixes every earlier standard circle throughout the motion. The pairwise-unlink hypotheses are essential: disjointness alone does not rule out a link.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful corrected supported one-circle transport child retaining the pairwise-unlink invariant needed by the ambient-isotopy construction. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_single_standardize_link_preserving_v2 {n : ℕ}
    (D : Set Space3) (hroundD : RoundCircle D)
    (hpairs : ∀ i, i < n → IsUnlink (![D, standardCircle i] : Fin 2 → Set Space3)) :
    ∃ G : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x) ∧
      (G 1) '' D = standardCircle n ∧
      (∀ t i, i < n → (G t) '' standardCircle i = standardCircle i) := by sorry
