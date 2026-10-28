-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_counts_with_correct_incidence
-- name    : WilliamsonShmoys.planar_drawing_face_counts_with_correct_incidence
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:55:47.635694+00:00
-- url     : https://prove2.me/theorems/78298d71-4d37-48a6-98ec-7b05bc48b5fa
-- title:
--   Euler and corrected facial incidence counts for a planar drawing
-- statement:
--   For a finite connected simple graph on at least three vertices with the supplied crossing-free drawing, there is a face count f satisfying Euler’s equation and the corrected facial incidence bound: three times the face count is at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_counts_with_correct_incidence
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by sorry
