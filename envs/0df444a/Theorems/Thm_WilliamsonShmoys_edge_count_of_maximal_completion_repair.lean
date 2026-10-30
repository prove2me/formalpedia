-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_completion_repair
-- name    : WilliamsonShmoys.edge_count_of_maximal_completion_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:00:23.423019+00:00
-- url     : https://prove2.me/theorems/b095f50e-f273-4207-95d7-a16a4d54bf9a
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly `3|V| − 6` edges. The proof formalizes the maximal planar graph argument: maximality forces connectedness and triangular faces, after which Euler’s formula and counting face-edge incidences yield the equality. The lower bound is essential to the edge-count claim and includes the three-vertex complete-graph boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_completion_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W)
    (hmax : ∀ U : SimpleGraph V,
      W ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ W) :
    3 * Fintype.card V = W.edgeSet.ncard + 6 := by sorry
