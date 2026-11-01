-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph__p2m_a5768c2e_2608_4566_9f99_2d604f38d755_a2
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_a5768c2e_2608_4566_9f99_2d604f38d755_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:46.331354+00:00
-- url     : https://prove2.me/theorems/15067ae2-6164-4683-8340-3852ef322251
-- title:
--   Spanning triangulation extension of a drawable graph
-- statement:
--   Every drawable finite simple graph with at least three vertices is contained in a drawable graph on the same vertices whose edge count is 3|V| - 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph__p2m_a5768c2e_2608_4566_9f99_2d604f38d755_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    Exists fun K : SimpleGraph V =>
      And (WilliamsonShmoys.HasPlanarDrawingOn K)
        (And (N <= K)
          (K.edgeSet.ncard + 6 = 3 * Fintype.card V)) := by
  sorry
