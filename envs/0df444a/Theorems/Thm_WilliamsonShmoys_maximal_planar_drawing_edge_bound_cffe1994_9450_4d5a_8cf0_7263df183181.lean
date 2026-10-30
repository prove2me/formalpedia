-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_bound_cffe1994_9450_4d5a_8cf0_7263df183181
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_bound_cffe1994_9450_4d5a_8cf0_7263df183181
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:13:28.07557+00:00
-- url     : https://prove2.me/theorems/636305c2-3142-4efd-9d82-4706aad84857
-- title:
--   Edge lower bound for an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal graph with the specified crossing-free drawing and at least three vertices has at least 3|V| − 6 edges. The proof must show the relevant maximal planar structure from the given drawing predicate and then formalize Euler’s formula and face-edge incidence counting; the three-vertex boundary case is covered by the same lower-bound argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_drawing_edge_bound_cffe1994_9450_4d5a_8cf0_7263df183181
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : forall N : SimpleGraph V,
      M <= N ->
      WilliamsonShmoys.HasPlanarDrawingOn N ->
      N = M) :
    3 * Fintype.card V - 6 <= M.edgeSet.ncard := by sorry
