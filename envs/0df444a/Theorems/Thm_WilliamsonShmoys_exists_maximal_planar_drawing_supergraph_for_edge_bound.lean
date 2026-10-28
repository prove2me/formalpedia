-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_for_edge_bound
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_for_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:29:22.968123+00:00
-- url     : https://prove2.me/theorems/fc913192-c4b7-4af6-8825-3b6a76067cd1
-- title:
--   Existence of a maximal drawable supergraph for the edge bound
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable supergraph maximal among drawable supergraphs on that type, and its edge count is no larger than the maximal graph's edge count. The boundary case with no additional drawable edges is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_for_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧ HasPlanarDrawingOn M ∧
      (∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M) ∧
      N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
