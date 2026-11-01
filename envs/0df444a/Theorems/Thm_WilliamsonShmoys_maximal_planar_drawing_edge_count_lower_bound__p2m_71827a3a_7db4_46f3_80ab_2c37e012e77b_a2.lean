-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:57:46.261451+00:00
-- url     : https://prove2.me/theorems/9667c397-02c4-4afb-ad3c-3d8252f0b79d
-- title:
--   Maximal planar drawing edge count lower bound
-- statement:
--   An edge-maximal graph with a crossing-free drawing and at least three vertices has at least 3n − 6 edges. This removes the lower-bound part of the parent; maximality rules out any drawable strict supergraph, so a plane embedding has only triangular faces, after which Euler’s formula and face-edge incidence counting give the bound. The n = 3 boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V)
    (hmax : ∀ M' : SimpleGraph V, M ≤ M' →
      WilliamsonShmoys.HasPlanarDrawingOn M' → M' = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by
  sorry
