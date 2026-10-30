-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:14.221997+00:00
-- url     : https://prove2.me/theorems/706d02aa-87d3-4c47-be20-96ce2bbf8d05
-- title:
--   Planar drawings bound the number of edges
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most three times its vertex count minus six edges. The decidable-adjacency instance makes the edge finset available in the statement. This child removes the geometric topology from the target proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_5e2c5d47_5385_4c28_8f25_877ce4670fc9_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
