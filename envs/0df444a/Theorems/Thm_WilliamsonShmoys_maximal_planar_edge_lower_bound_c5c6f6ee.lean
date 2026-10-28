-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c5c6f6ee
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:50:00.051746+00:00
-- url     : https://prove2.me/theorems/07130f49-9b32-461e-902c-b2aad76671c0
-- title:
--   Maximal planarity edge lower bound
-- statement:
--   If a graph on at least three vertices has the supplied planar drawing and is inclusion-maximal among drawable simple graphs on that same vertex type, then it has at least 3n − 6 edges. This removes the part of the target that uses maximality and preserves its exact quantification over same-type supergraphs. A proof route is to formalize the drawing as a planar embedding, establish that maximality forces connectedness and triangular faces, and apply Euler’s formula. The n = 3 boundary case is retained. The embedding and face arguments are the main remaining topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_c5c6f6ee
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
