-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:52.897206+00:00
-- url     : https://prove2.me/theorems/620608d3-0799-426b-beeb-eff4e8e41716
-- title:
--   Edge count of a maximal simple planar graph
-- statement:
--   An inclusion-maximal finite simple graph admitting the specified crossing-free drawing, with at least three vertices, has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_833458fe_f209_438f_86e7_1012b8725315_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) → L = K)
    (hcard : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
