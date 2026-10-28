-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_completion_91679e32
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_for_completion_91679e32
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T00:14:02.516159+00:00
-- url     : https://prove2.me/theorems/0793cb93-0291-4b9c-9b25-9b0362d0ce46
-- title:
--   A maximal drawable graph has the planar edge count
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type has exactly 3|V| - 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_for_completion_91679e32
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNplanar : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V)
    (hNmaximal : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
