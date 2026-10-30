-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_edge_count_lower_bound
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:30:58.258028+00:00
-- url     : https://prove2.me/theorems/9a20304d-6b61-40fc-b789-63f3673931bb
-- title:
--   Edge lower bound for an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal graph with the supplied planar drawing on at least three vertices has at least 3n−6 edges. This isolates the topological edge-count argument needed to contradict the parent's strict edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hMax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by sorry
