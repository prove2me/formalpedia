-- Prove2me | Theorems.Thm_BookSixth_round_circle_snoc_transport_compose_v3
-- name    : BookSixth.round_circle_snoc_transport_compose_v3
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:40:47.577844+00:00
-- url     : https://prove2.me/theorems/301c14de-1336-43ed-aa00-f70597c918c1
-- title:
--   Chapter 15 bridge: compose a supported prefix and a supported circle transport
-- statement:
--   A supported isotopy carrying the old family to its standard circles can be composed with a single-circle transport which fixes those standard circles at the final time. The resulting ambient isotopy carries the old family and the appended circle to their assigned standard circles simultaneously.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Corrected source-faithful composition child for BookSixth.round_circle_snoc_transport. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_snoc_transport_compose_v3 {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (K : ℝ → Space3 ≃ₜ Space3)
    (G : ℝ → Space3 ≃ₜ Space3)
    (hK : Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x))
    (hG : Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x))
    (hKold : ∀ i, (K 1) '' C i = standardCircle i.val)
    (hKnew : ∀ t, K t '' D = D)
    (hGnew : (G 1) '' D = standardCircle n)
    (hGprefix : ∀ i : Fin n, (G 1) '' standardCircle i.val = standardCircle i.val) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ i, (H 1) '' C i = standardCircle i.val) ∧
      (H 1) '' D = standardCircle n := by sorry
