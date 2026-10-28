-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_completion_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- name    : WilliamsonShmoys.planar_drawingOn_triangulation_completion_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:26:07.606696+00:00
-- url     : https://prove2.me/theorems/73897ec1-3ca7-4610-af6a-93823533007f
-- title:
--   Drawable triangulation completion with exact edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly 3|V|−6 edges. The parent uses this completion and maximality to identify its edge set with the original graph’s edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_triangulation_completion_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
