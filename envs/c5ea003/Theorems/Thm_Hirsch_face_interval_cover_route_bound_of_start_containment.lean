-- Prove2me | Theorems.Thm_Hirsch_face_interval_cover_route_bound_of_start_containment
-- name    : Hirsch.face_interval_cover_route_bound_of_start_containment
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T14:54:40.430087+00:00
-- url     : https://prove2.me/theorems/ae57fc5c-9c88-45e9-b717-eb8ea9fb6cfe
-- title:
--   Start containment supplies portals for crossing extreme-face interval repair
-- statement:
--   A finite extreme-face interval cover routes its endpoint vertices within the sum of the face diameter budgets when every later interval start that occurs before an earlier interval ends lies in the earlier supporting face. The later start is then automatically a shared parent-vertex portal between the two overlapping faces.
-- source:
--   Verified Lean theorem from jjoshua2/prove2me-work PR #48.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem face_interval_cover_route_bound_of_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (hverts : ∀ i, w (s i) ∈ extremePoints ℝ P ∧ w (t i) ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by sorry

end Hirsch
