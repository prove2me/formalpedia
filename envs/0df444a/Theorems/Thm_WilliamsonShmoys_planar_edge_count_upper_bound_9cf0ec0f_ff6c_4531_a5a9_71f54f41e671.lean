-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:28:24.868576+00:00
-- url     : https://prove2.me/theorems/b97309e8-bb0a-4bb4-8a28-f24a036d846f
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices has at most 3|V|−6 edges. This removes the upper-bound half of the target. A proof route is to derive planar Euler counting from the drawing, then use that each face boundary has length at least three when there are at least three vertices. The vertex-count hypothesis is essential to this face-length argument and is retained explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_9cf0ec0f_ff6c_4531_a5a9_71f54f41e671
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    (K.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
