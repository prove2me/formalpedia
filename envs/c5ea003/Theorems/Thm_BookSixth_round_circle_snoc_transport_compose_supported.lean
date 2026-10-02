-- Prove2me | Theorems.Thm_BookSixth_round_circle_snoc_transport_compose_supported
-- name    : BookSixth.round_circle_snoc_transport_compose_supported
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-23T22:36:41.62084+00:00
-- url     : https://prove2.me/theorems/72ee312f-7501-4b14-b1b0-84cc28f873bd
-- title:
--   Chapter 15 bridge: compose a supported prefix and appended-circle transport
-- statement:
--   Suppose a supported isotopy `K` sends the old circles to their assigned standard circles while fixing the appended circle `D`, and an appended-circle isotopy `G` sends `D` to `standardCircle n` while preserving every old standard circle. Then the time-ordered composition `H t = G t ∘ K t` is a continuous ambient isotopy that simultaneously standardizes all components. The preservation premise on `G` is essential; without it, the images of the old components are not determined by the data.
-- source:
--   Corrected pure composition child for the Chapter 15 transport construction in Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100, https://doi.org/10.1007/978-3-662-57265-8_15. It repairs the original decomposition by requiring the appended-circle transport to preserve the old standard family.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_snoc_transport_compose_supported {n : ℕ}
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
    (hGstandard : ∀ i : Fin n,
      (G 1) '' standardCircle i.val = standardCircle i.val) :
    ∃ H : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
      (∀ x, H 0 x = x) ∧
      (∀ i, (H 1) '' C i = standardCircle i.val) ∧
      (H 1) '' D = standardCircle n := by sorry
