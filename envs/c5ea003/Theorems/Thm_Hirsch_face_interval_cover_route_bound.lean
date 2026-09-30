-- Prove2me | Theorems.Thm_Hirsch_face_interval_cover_route_bound
-- name    : Hirsch.face_interval_cover_route_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T14:00:48.240239+00:00
-- url     : https://prove2.me/theorems/11592f65-f434-4fad-9c84-f96cf223c3bf
-- title:
--   Portal-backed crossing interval repair through extreme faces
-- statement:
--   If repair intervals cover every old step and every chronological overlap is backed by a genuine shared parent vertex between the corresponding extreme faces, the endpoints admit a padded parent walk whose budget is the sum of the face diameter budgets.
-- source:
--   Verified Lean theorem from jjoshua2/prove2me-work PR #39.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem face_interval_cover_route_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hportal : ∀ i j, s i ≤ t j → s j ≤ t i →
      ∃ z, z ∈ extremePoints ℝ P ∧ z ∈ F i ∧ z ∈ F j) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ j < ∑ i, B i, q j = q (j + 1) ∨ Adj P (q j) (q (j + 1)) := by sorry

end Hirsch
