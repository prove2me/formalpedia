-- Prove2me | Theorems.Thm_Hirsch_geodesic_face_disjoint_tail_bound
-- name    : Hirsch.geodesic_face_disjoint_tail_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T02:13:22.336178+00:00
-- url     : https://prove2.me/theorems/16f7c90c-1721-4cfe-aa86-52c761ff99c1
-- title:
--   Order-sensitive extreme-face tail bound for graph diameter
-- statement:
--   Suppose every selected extreme face has intrinsic graph diameter at most B. For every start vertex u, suppose at most K vertices share no selected face with u. If the vertex graph is connected, then the whole graph has padded diameter at most B+K.
-- source:
--   Verified Polynomial Hirsch graph-geometry helper developed in the September 2026 formalization; see jjoshua2/prove2me-work PR #27.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem geodesic_face_disjoint_tail_bound
    {ι : Type*} (d B K : ℕ)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hF : ∀ i, IsExtreme ℝ P (F i)) (hFD : ∀ i, DiamLE (F i) B)
    (htails : ∀ u ∈ extremePoints ℝ P,
      ∃ T : Finset (EuclideanSpace ℝ (Fin d)), T.card ≤ K ∧
        ∀ x ∈ extremePoints ℝ P, (∀ i, u ∈ F i → x ∉ F i) → x ∈ T)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P (B + K) := by sorry

end Hirsch
