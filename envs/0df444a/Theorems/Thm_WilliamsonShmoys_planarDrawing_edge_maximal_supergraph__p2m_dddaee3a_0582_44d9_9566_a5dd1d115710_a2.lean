-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_maximal_supergraph__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
-- name    : WilliamsonShmoys.planarDrawing_edge_maximal_supergraph__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:40.315277+00:00
-- url     : https://prove2.me/theorems/cf1fad93-82bb-45b4-92ca-a77558fa3813
-- title:
--   Choose an edge-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_edge_maximal_supergraph__p2m_dddaee3a_0582_44d9_9566_a5dd1d115710_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
        ∀ H : SimpleGraph V,
          M ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ M := by sorry
