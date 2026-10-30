-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count_for_completion
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:53:18.790983+00:00
-- url     : https://prove2.me/theorems/cd02c495-7df0-4ed9-9dfe-5745cc6a5964
-- title:
--   Exact edge count for a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices with no proper drawable supergraph has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count_for_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
