-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_a0798f51_6e18_4401_9598_620a32b64bfd
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_a0798f51_6e18_4401_9598_620a32b64bfd
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:35:37.062806+00:00
-- url     : https://prove2.me/theorems/c701c0b0-a596-4943-b459-a7991aaff793
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly `3 * Fintype.card V - 6` edges. Its proof uses the maximal-planar-graph edge count via triangular faces, Euler’s formula, and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_a0798f51_6e18_4401_9598_620a32b64bfd
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hMplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V, M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N -> N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
