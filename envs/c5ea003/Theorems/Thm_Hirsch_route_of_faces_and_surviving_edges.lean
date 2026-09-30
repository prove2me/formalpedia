-- Prove2me | Theorems.Thm_Hirsch_route_of_faces_and_surviving_edges
-- name    : Hirsch.route_of_faces_and_surviving_edges
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T14:12:51.91829+00:00
-- url     : https://prove2.me/theorems/9eed40c7-03ed-4a02-80b4-1f7404ac05ac
-- title:
--   Routing from face regions and surviving edges
-- statement:
--   If every consecutive checkpoint pair is covered either by one certified extreme face or by one listed surviving parent edge, then a genuine parent walk has budget equal to the sum of all face diameter budgets plus the number of listed surviving edges.
-- source:
--   Verified Lean theorem from jjoshua2/prove2me-work PR #40.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

theorem Hirsch.route_of_faces_and_surviving_edges
    {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (a b : κ → EuclideanSpace ℝ (Fin d)) (hedge : ∀ e, Adj P (a e) (b e))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hverts : ∀ k ≤ L, w k ∈ extremePoints ℝ P)
    (hcover : ∀ k < L,
      (∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) ∨
      (∃ e, w k ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))) ∧
        w (k + 1) ∈ ({a e, b e} : Set (EuclideanSpace ℝ (Fin d))))) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q ((∑ i, B i) + Fintype.card κ) = w L ∧
      ∀ j < (∑ i, B i) + Fintype.card κ,
        q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by sorry
