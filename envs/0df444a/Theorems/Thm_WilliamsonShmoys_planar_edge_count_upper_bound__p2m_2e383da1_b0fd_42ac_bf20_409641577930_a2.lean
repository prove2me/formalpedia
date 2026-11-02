-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:45:05.727219+00:00
-- url     : https://prove2.me/theorems/1450b57d-ff3f-4f0e-9779-6941f1e67e4b
-- title:
--   Planar graphs have at most three n minus six edges
-- statement:
--   Every finite simple graph on an ordered vertex type with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_2e383da1_b0fd_42ac_bf20_409641577930_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
