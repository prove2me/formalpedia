-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound_06232b3e
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_06232b3e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:18:29.013983+00:00
-- url     : https://prove2.me/theorems/537cdc2c-cf72-4d49-81fe-49e7ce1cc744
-- title:
--   Lower bound for a maximal drawable graph
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges. Maximality rules out a disconnected drawing and any face that permits adding a missing edge; the resulting triangulation gives the bound by Euler’s formula and face-edge incidence counting. At three vertices maximality forces all three edges. This supplies the target’s lower-bound obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound_06232b3e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K → K = L) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
