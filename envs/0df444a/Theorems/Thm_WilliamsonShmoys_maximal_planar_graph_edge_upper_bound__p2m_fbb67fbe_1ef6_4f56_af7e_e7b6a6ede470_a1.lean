-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_upper_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:15.609342+00:00
-- url     : https://prove2.me/theorems/d428652f-4806-46f7-95cc-5b75c77bec4b
-- title:
--   Edge upper bound for a planar drawing
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The proof route is to obtain a plane embedding, apply Euler’s formula, and count edge-face incidences; simplicity and the vertex lower bound handle the face-degree boundary cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_upper_bound__p2m_fbb67fbe_1ef6_4f56_af7e_e7b6a6ede470_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    M.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
