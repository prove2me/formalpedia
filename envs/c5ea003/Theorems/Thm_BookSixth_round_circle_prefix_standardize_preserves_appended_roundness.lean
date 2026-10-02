-- Prove2me | Theorems.Thm_BookSixth_round_circle_prefix_standardize_preserves_appended_roundness
-- name    : BookSixth.round_circle_prefix_standardize_preserves_appended_roundness
-- status  : Open
-- author  : @WillR
-- created : 2026-09-24T07:08:34.994975+00:00
-- url     : https://prove2.me/theorems/067c6497-db85-4def-9301-8928d62f3503
-- title:
--   Chapter 15 bridge: prefix standardization preserves appended roundness
-- statement:
--   When an already-unlinked family of round circles is carried to its assigned standard circles, the ambient isotopy can be chosen so that the appended round circle remains a genuine round circle in its image. The appended circle need not be fixed pointwise or setwise; only its roundness is retained. This is the geometric support condition needed before transporting that image to the next standard circle.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful corrected prefix-transport child retaining the appended round-circle condition needed for the ambient-isotopy construction. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_prefix_standardize_preserves_appended_roundness 
    {n : ℕ} (C : Fin n → Set Space3) (D : Set Space3)
    (hroundC : ∀ i, RoundCircle (C i)) (hroundD : RoundCircle D)
    (hdisjointC : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hdisjointD : ∀ i, Disjoint (C i) D)
    (hprefix : IsUnlink C)
    (hpairs : ∀ i, IsUnlink (![C i, D] : Fin 2 → Set Space3)) :
    ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (∀ i, (K 1) '' C i = standardCircle i.val) ∧
      RoundCircle (K 1 '' D) := by sorry
