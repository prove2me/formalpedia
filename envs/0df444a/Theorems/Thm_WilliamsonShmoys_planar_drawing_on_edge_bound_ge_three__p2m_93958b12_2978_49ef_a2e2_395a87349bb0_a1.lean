-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_edge_bound_ge_three__p2m_93958b12_2978_49ef_a2e2_395a87349bb0_a1
-- name    : WilliamsonShmoys.planar_drawing_on_edge_bound_ge_three__p2m_93958b12_2978_49ef_a2e2_395a87349bb0_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T12:30:33.565998+00:00
-- url     : https://prove2.me/theorems/81eeb5a9-4898-4e78-994a-d8befd1f7cc2
-- title:
--   Planar drawing edge bound for at least three vertices
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges. The child isolates the Euler-formula and face-counting argument; the parent handles the smaller vertex-count boundary cases directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_on_edge_bound_ge_three__p2m_93958b12_2978_49ef_a2e2_395a87349bb0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V ≤ N.edgeFinset.card + 6) := by sorry
