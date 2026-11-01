-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_edge_bound__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
-- name    : WilliamsonShmoys.planar_face_count_edge_bound__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:26.304278+00:00
-- url     : https://prove2.me/theorems/567ac867-6aa3-418e-8ffa-0d4ebf0bd3c5
-- title:
--   Edge bound from Euler face-count inequalities
-- statement:
--   If the vertex count is at least three and a natural face count satisfies Euler’s equation and the total face-degree bound, then the graph has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_edge_bound__p2m_45b42f5d_e929_44e5_b683_b600a07db038_a3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hcard : 3 ≤ Fintype.card V) (hfaces : ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 ∧ 3 * f ≤ 2 * M.edgeFinset.card) : M.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by sorry
