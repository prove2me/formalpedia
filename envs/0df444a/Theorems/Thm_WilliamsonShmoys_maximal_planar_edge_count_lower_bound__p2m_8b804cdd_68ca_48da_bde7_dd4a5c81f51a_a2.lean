-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:32.417005+00:00
-- url     : https://prove2.me/theorems/a5768c2e-2608-4566-9f99-2d604f38d755
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph with at least three vertices has at least 3|V| - 6 edges. Maximality rules out disconnected components and nontriangular faces: a missing edge or diagonal could otherwise be added while retaining a planar drawing. Euler's formula and edge-face incidence then give the lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_8b804cdd_68ca_48da_bde7_dd4a5c81f51a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K -> N <= K -> K = N)
    (hcard : 3 <= Fintype.card V) :
    3 * Fintype.card V <= N.edgeSet.ncard + 6 := by
  sorry
