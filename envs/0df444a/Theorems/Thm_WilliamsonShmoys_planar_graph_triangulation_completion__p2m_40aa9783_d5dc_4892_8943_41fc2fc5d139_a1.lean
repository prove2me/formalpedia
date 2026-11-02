-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_completion__p2m_40aa9783_d5dc_4892_8943_41fc2fc5d139_a1
-- name    : WilliamsonShmoys.planar_graph_triangulation_completion__p2m_40aa9783_d5dc_4892_8943_41fc2fc5d139_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:33:43.947009+00:00
-- url     : https://prove2.me/theorems/f3f7a3a7-d237-45a5-b1fd-f31e0f1c8fc4
-- title:
--   Triangulation completion of a drawable graph
-- statement:
--   Any drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex set whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_triangulation_completion__p2m_40aa9783_d5dc_4892_8943_41fc2fc5d139_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hplanar : HasPlanarDrawingOn K) :
    ∃ J : SimpleGraph V, K.edgeSet ⊆ J.edgeSet ∧
      HasPlanarDrawingOn J ∧
      J.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
