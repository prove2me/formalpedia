-- Prove2me | Theorems.Thm_BookSixth_round_circle_snoc_transport_compose_v4
-- name    : BookSixth.round_circle_snoc_transport_compose_v4
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-24T06:43:17.497571+00:00
-- url     : https://prove2.me/theorems/c587e2de-39cc-4a22-ad42-b0673f16cc6e
-- title:
--   Chapter 15 bridge: compose prefix transport with supported circle transport
-- statement:
--   Compose an isotopy `L` carrying the old family to its standard circles with an isotopy `G` that fixes those standard circles and carries `L 1` applied to the appended circle to the next standard circle. The resulting isotopy `H t = G t ∘ L t` carries every old component and the appended circle to their assigned standard circles.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Corrected source-faithful composition child for BookSixth.round_circle_snoc_transport; it does not require a false prefix isotopy fixing the appended circle. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_snoc_transport_compose_v4 {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (L : ℝ → Space3 ≃ₜ Space3)
    (G : ℝ → Space3 ≃ₜ Space3)
    (hL : Continuous (fun p : ℝ × Space3 => L p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (L p.1).symm p.2) ∧
      (∀ x, L 0 x = x))
    (hG : Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x))
    (hLold : ∀ i, (L 1) '' C i = standardCircle i.val)
    (hGnew : (G 1) '' (L 1) '' D = standardCircle n)
    (hGprefix : ∀ i : Fin n, (G 1) '' standardCircle i.val = standardCircle i.val) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ i, (H 1) '' C i = standardCircle i.val) ∧
      (H 1) '' D = standardCircle n := by sorry
