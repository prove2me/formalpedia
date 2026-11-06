-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:29.985681+00:00
-- url     : https://prove2.me/theorems/71827a3a-7db4-46f3-80ab-2c37e012e77b
-- title:
--   Count edges in an edge-maximal planar graph
-- statement:
--   An edge-maximal finite simple graph with a planar drawing and at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_eb26a690_3fb7_4c37_81bf_9f642ccd4501_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ M' : SimpleGraph V, M <= M' →
      WilliamsonShmoys.HasPlanarDrawingOn M' → M' = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
