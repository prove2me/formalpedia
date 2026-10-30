-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:40.427986+00:00
-- url     : https://prove2.me/theorems/f64d1837-5003-4948-9974-ab50e71d546a
-- title:
--   Planar edge count upper bound
-- statement:
--   For any finite simple graph with the supplied crossing-free drawing and at least three vertices, its edge count is at most 3|V|−6, including when the graph is disconnected. This is a new argument from the drawing definition: extend the graph to a maximal drawable supergraph on the same finite vertex type, then use the plane graph face count and Euler’s formula. It removes the target’s upper-bound obligation; the topological step is still to justify completion and face counting for this arc-based drawing predicate. The |V| ≥ 3 condition is essential to the bound and covers the triangle boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V)) :
    LE.le (K.edgeSet.ncard + 6) (3 * Fintype.card V) := by
  sorry
