-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:35:11.716837+00:00
-- url     : https://prove2.me/theorems/f1c98aeb-0d96-40c6-9368-4648e8311f09
-- title:
--   Planar drawing completion with the planar edge count
-- statement:
--   A finite simple graph on at least three ordered vertices with a crossing-free drawing has a crossing-free supergraph on the same vertex set whose edge count is exactly 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
