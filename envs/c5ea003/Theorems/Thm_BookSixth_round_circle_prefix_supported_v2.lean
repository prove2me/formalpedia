-- Prove2me | Theorems.Thm_BookSixth_round_circle_prefix_supported_v2
-- name    : BookSixth.round_circle_prefix_supported_v2
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-23T22:38:36.66633+00:00
-- url     : https://prove2.me/theorems/0e8688d8-cc38-4cb2-bc21-8a74bd34808e
-- title:
--   Chapter 15 bridge: pairwise-aware supported prefix extension
-- statement:
--   When the existing family is an unlink and each old component is pairwise unlinked with the appended circle, the ambient isotopy carrying the existing family to the standard circles can be chosen to fix the appended round circle throughout the motion. The pairwise hypothesis is essential: disjoint round circles may still form a nontrivial link.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Corrected source-faithful supported-extension child retaining the pairwise-unlink hypothesis of BookSixth.round_circle_snoc_transport. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_prefix_supported_v2 {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
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
      (∀ t, K t '' D = D) := by sorry
