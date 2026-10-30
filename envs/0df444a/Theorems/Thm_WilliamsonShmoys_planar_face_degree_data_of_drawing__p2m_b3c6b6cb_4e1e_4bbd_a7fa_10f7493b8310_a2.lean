-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_degree_data_of_drawing__p2m_b3c6b6cb_4e1e_4bbd_a7fa_10f7493b8310_a2
-- name    : WilliamsonShmoys.planar_face_degree_data_of_drawing__p2m_b3c6b6cb_4e1e_4bbd_a7fa_10f7493b8310_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:12:39.549746+00:00
-- url     : https://prove2.me/theorems/c5ad35b6-4de7-43d3-a938-26b42046546e
-- title:
--   Extract Euler face degrees from a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing admits a finite list of face degrees satisfying Euler’s relation, total degree twice the edge count, and degree at least three for every face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_face_degree_data_of_drawing__p2m_b3c6b6cb_4e1e_4bbd_a7fa_10f7493b8310_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ (m : Nat) (degree : Fin m → Nat),
      Fintype.card V + m = H.edgeSet.ncard + 2 ∧
      (∑ f : Fin m, degree f) = 2 * H.edgeSet.ncard ∧
      ∀ f, 3 <= degree f := by sorry
