-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_graph_exact_edge_count__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
-- name    : WilliamsonShmoys.exists_planar_graph_exact_edge_count__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:32.500878+00:00
-- url     : https://prove2.me/theorems/9b625ce0-21a3-499d-bb1b-40258fa2706e
-- title:
--   Existence of a drawable graph attaining the planar edge bound
-- statement:
--   Every finite linearly ordered vertex type with at least three elements admits a drawable simple graph with exactly three times its cardinality minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_graph_exact_edge_count__p2m_022fc3fe_2112_4838_9b2a_056c25ecda08_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
