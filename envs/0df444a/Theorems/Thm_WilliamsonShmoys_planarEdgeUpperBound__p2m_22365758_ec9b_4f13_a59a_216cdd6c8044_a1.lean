-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarEdgeUpperBound__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a1
-- name    : WilliamsonShmoys.planarEdgeUpperBound__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:40:07.658708+00:00
-- url     : https://prove2.me/theorems/7aba0fb5-3fb8-41a1-bd51-7eebe593bbaa
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every simple graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarEdgeUpperBound__p2m_22365758_ec9b_4f13_a59a_216cdd6c8044_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel G.Adj := dG
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
