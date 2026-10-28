-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_maximal_edge_count
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_maximal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:50:43.080988+00:00
-- url     : https://prove2.me/theorems/b0b8199f-bdb2-47d6-8551-67174697395f
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite simple graph on at least three vertices that is maximal among its planar-drawing supergraphs has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_ed91fffc_a32b_46e0_9209_f57c29a4258c_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K <= L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L <= K) :
    (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
