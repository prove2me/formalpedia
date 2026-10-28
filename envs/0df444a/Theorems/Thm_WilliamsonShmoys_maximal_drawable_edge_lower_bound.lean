-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:41:11.800324+00:00
-- url     : https://prove2.me/theorems/4658431d-1db7-4948-87db-836d6a8505d2
-- title:
--   Edge lower bound for maximal drawable graphs
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has at least 3|V|−6 edges. The proof route is to extend its embedding to a maximal planar embedding, show its faces are triangles, and apply Euler's formula and face-edge counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
