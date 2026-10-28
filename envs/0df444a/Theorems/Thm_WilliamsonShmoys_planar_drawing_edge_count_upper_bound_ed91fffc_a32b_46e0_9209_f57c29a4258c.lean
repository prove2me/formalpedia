-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:21:57.088059+00:00
-- url     : https://prove2.me/theorems/05250361-edf9-4bba-b0bb-f1c9e6abc2aa
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A finite simple graph with at least three vertices and the specified crossing-free arc drawing has at most 3|V| − 6 edges. This gives the upper half of the parent’s edge-count equality. A proof route is to derive a plane embedding and combine Euler counting with face-length bounds, including the disconnected case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound_ed91fffc_a32b_46e0_9209_f57c29a4258c
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    (M.edgeSet.ncard : Int) <=
      (3 : Int) * (Fintype.card V : Int) - 6 := by sorry
