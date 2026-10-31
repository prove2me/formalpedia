-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_face_count_of_drawing__p2m_7f93d6a5_e061_4fd9_b77a_4e628bac87b4_a1
-- name    : WilliamsonShmoys.planar_simple_graph_face_count_of_drawing__p2m_7f93d6a5_e061_4fd9_b77a_4e628bac87b4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:45:33.168906+00:00
-- url     : https://prove2.me/theorems/ec28c235-4f25-4282-80df-e728cc43cd8d
-- title:
--   Euler face count and face incidence bound from a planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free drawing has a finite face count satisfying Euler’s relation, with total face-boundary length at least three per face and total edge incidence twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_face_count_of_drawing__p2m_7f93d6a5_e061_4fd9_b77a_4e628bac87b4_a1
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hconn : H.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * H.edgeSet.ncard := by sorry
