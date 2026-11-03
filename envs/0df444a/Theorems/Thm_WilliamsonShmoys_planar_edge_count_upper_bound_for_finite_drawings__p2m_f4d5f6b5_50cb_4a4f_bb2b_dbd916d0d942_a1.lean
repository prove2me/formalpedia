-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_finite_drawings__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_finite_drawings__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:09:21.688918+00:00
-- url     : https://prove2.me/theorems/af29cc6c-d384-47b6-b521-c5970719d714
-- title:
--   Planar edge count upper bound for finite drawings
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V|−6 edges, including when it is disconnected. This removes the upper-bound half of the parent’s edge-count argument. A proof route is to connect components in the plane, then use Euler’s formula and the fact that each face boundary has length at least three. The explicit arc representation makes establishing the needed face facts the main formal work for this child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_finite_drawings__p2m_f4d5f6b5_50cb_4a4f_bb2b_dbd916d0d942_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    M.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
