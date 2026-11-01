-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_boundary_lower_bound__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
-- name    : WilliamsonShmoys.planar_face_count_boundary_lower_bound__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:58.512505+00:00
-- url     : https://prove2.me/theorems/3a4c1f5e-1776-4c15-8093-87a5faec746f
-- title:
--   Lower bound on total face-boundary length
-- statement:
--   For the face count of a connected simple graph with at least three vertices and the supplied crossing-free drawing, the sum of face-boundary lengths is at least three per face and equals twice the number of edges. Thus three times the face count is at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_boundary_lower_bound__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) (hcard : 3 ≤ Fintype.card V) (f : ℕ) (hEuler : Fintype.card V + f = M.edgeFinset.card + 2) : 3 * f ≤ 2 * M.edgeFinset.card := by sorry
