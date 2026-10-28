-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_face_equations_9ae33b99
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_face_equations_9ae33b99
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:50:49.832417+00:00
-- url     : https://prove2.me/theorems/09e79c63-e21c-48cc-8d84-f87d06d25208
-- title:
--   Maximal planar drawing edge lower bound for face equations
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set has at least 3|V|−6 edges. This supplies the lower bound; a proof route is to establish that maximality forces a triangulated planar embedding and then apply Euler counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_face_equations_9ae33b99
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
