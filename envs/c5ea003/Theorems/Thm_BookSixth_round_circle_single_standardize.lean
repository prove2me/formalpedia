-- Prove2me | Theorems.Thm_BookSixth_round_circle_single_standardize
-- name    : BookSixth.round_circle_single_standardize
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:09:49.085632+00:00
-- url     : https://prove2.me/theorems/57b4c109-19d1-44b6-9291-0b9ef979db2c
-- title:
--   Chapter 15 bridge: standardize one round circle
-- statement:
--   A single genuine round circle can be carried to any assigned separated standard circle by a continuous ambient isotopy. This is the one-circle geometric transport step used when appending a circle.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful one-circle geometric child for BookSixth.round_circle_snoc_transport. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_single_standardize (D : Set Space3)
    (hroundD : RoundCircle D) (k : ℕ) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (H 1) '' D = standardCircle k := by sorry
