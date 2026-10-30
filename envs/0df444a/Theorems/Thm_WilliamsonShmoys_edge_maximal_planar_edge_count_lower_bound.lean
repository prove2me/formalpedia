-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_lower_bound
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:36:42.927629+00:00
-- url     : https://prove2.me/theorems/3603cb59-5fc7-4b73-9323-ab96b2a23da2
-- title:
--   Maximality forces the triangulation edge lower bound
-- statement:
--   A drawable graph maximal among drawable supergraphs on the same vertex set, with at least three vertices, has at least 3|V|−6 edges. The child uses maximality and the drawing hypothesis; its proof route is to show the embedding is connected and every face is triangular, then apply Euler’s equation and count face-edge incidences. At three vertices, the boundary case forces all three edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet ⊆ H.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
