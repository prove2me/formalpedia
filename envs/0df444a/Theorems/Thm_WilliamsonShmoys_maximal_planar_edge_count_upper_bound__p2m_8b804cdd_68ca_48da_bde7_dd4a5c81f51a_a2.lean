-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:32.153132+00:00
-- url     : https://prove2.me/theorems/eb26a690-3fb7-4c37-81bf-9f642ccd4501
-- title:
--   Edge upper bound for a finite graph with a planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| - 6 edges. This gives one inequality in the target. A proof route counts faces in a planar embedding using Euler's formula and the fact that each face has boundary length at least three, with separate bookkeeping for disconnected drawings.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
