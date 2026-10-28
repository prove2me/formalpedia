-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_b3dab4f4
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_b3dab4f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:31:20.410827+00:00
-- url     : https://prove2.me/theorems/373dcc1c-b5a0-431f-b2a4-dc3190258bf0
-- title:
--   Maximal drawable graphs meet the triangulation lower bound
-- statement:
--   If a finite simple graph on at least three vertices has a crossing-free drawing and no strictly larger drawable supergraph on the same vertex type, then it has at least 3|V|−6 edges. A proof route is to show maximality forces every face to be triangular, then apply Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_b3dab4f4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) :
    3 * Fintype.card V - 6 <= L.edgeSet.ncard := by sorry
