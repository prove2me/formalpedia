-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_completion_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- name    : WilliamsonShmoys.maximal_planar_supergraph_completion_task_2f486b23_4a17_4b27_89f1_8ee712518760
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:09:36.847926+00:00
-- url     : https://prove2.me/theorems/0f0b1829-7fd8-4ece-8af3-6c4cb33ade6b
-- title:
--   Maximal planar supergraph completion
-- statement:
--   Any finite graph with the supplied planar drawing and at least three vertices has an inclusion-maximal planar supergraph on the same vertex type. Maximize the edge count among the finite set of planar supergraphs of the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_completion_task_2f486b23_4a17_4b27_89f1_8ee712518760
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall M : SimpleGraph V, L <= M ->
        WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by sorry
