-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_dense_extension
-- name    : WilliamsonShmoys.planar_graph_has_dense_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:08:54.427471+00:00
-- url     : https://prove2.me/theorems/6e62a26d-6a7c-4e08-9d6a-491a6df8336d
-- title:
--   Dense drawable supergraph extension
-- statement:
--   Every drawable graph on at least three vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges. The proof route is to complete the drawing to a maximal planar graph, handle disconnected components during completion, and apply Euler’s formula after showing maximality forces triangular faces. The work left in the parent is only to invoke maximality and transfer the edge bound back to the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_dense_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists P : SimpleGraph V, N <= P /\ WilliamsonShmoys.HasPlanarDrawingOn P /\
      3 * Fintype.card V - 6 <= P.edgeSet.ncard := by sorry
