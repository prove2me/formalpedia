-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_upper_bound_euler_exact_arcs
-- name    : WilliamsonShmoys.planar_drawingOn_edge_upper_bound_euler_exact_arcs
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:05:03.004004+00:00
-- url     : https://prove2.me/theorems/6b34fde2-2245-4245-afb7-422892f246b3
-- title:
--   Euler edge bound for the exact finite drawing predicate
-- statement:
--   A finite simple graph with at least three vertices and a drawing satisfying the exact `HasPlanarDrawingOn` predicate has at most 3|V|−6 edges. The proof route is Euler’s formula for the embedding induced by the arcs, together with the face-length bound for a simple graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_edge_upper_bound_euler_exact_arcs
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
