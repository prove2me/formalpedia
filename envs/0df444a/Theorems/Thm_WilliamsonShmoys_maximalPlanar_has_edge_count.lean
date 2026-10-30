-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanar_has_edge_count
-- name    : WilliamsonShmoys.maximalPlanar_has_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:41:15.178962+00:00
-- url     : https://prove2.me/theorems/570807d1-034b-400e-a623-bb3aff438dd2
-- title:
--   A maximal drawable graph has the planar extremal edge count
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly `3|V|−6` edges. A proof route is to establish triangular faces from maximality and apply Euler’s formula; the lower bound on the vertex count is preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanar_has_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, N.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
