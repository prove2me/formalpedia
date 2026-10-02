-- Prove2me | Theorems.Thm_BookSixth_round_circle_snoc_of_transport
-- name    : BookSixth.round_circle_snoc_of_transport
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T21:30:18.433206+00:00
-- url     : https://prove2.me/theorems/08bc82db-f9fb-4e4e-bbe4-453d235845e0
-- title:
--   Chapter 15 bridge: package a transport as an unlink
-- statement:
--   If one continuous ambient isotopy carries every component of a family to its assigned standard circle, then the family is an unlink by the canonical BookSixth definition. This packaging child is independent of the geometric transport construction.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Source-faithful IsUnlink packaging child for BookSixth.round_circle_unlink_snoc. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_snoc_of_transport {n : ℕ} (C : Fin n → Set Space3) (D : Set Space3)
    (H : ∃ K : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x) ∧
      (∀ i, (K 1) '' C i = standardCircle i.val) ∧
      (K 1) '' D = standardCircle n) :
    IsUnlink (Fin.snoc C D) := by sorry
