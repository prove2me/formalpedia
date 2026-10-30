-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_9ae33b99
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_9ae33b99
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:26:21.96109+00:00
-- url     : https://prove2.me/theorems/a4bb2f6d-f8da-47b0-a688-46bb3d3285fa
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   An inclusion-maximal simple planar graph on a fixed finite vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_9ae33b99
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hmax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K = H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
