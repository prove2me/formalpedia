-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:19:31.847427+00:00
-- url     : https://prove2.me/theorems/24cd5df2-f06e-484a-a9e0-671b5163ec2a
-- title:
--   Maximal planar edge lower bound
-- statement:
--   A simple graph on at least three vertices that is maximal among graphs admitting a crossing-free drawing has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f9d76db2_d767_4642_99f4_dff7d260828e_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : forall M' : SimpleGraph V, M <= M' -> WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) : 3 * Fintype.card V - 6 <= M.edgeSet.ncard := by sorry
