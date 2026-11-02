-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:42:52.149836+00:00
-- url     : https://prove2.me/theorems/17d4ecd1-7eb5-4091-99bc-0efffdc2e9e3
-- title:
--   Euler upper bound for planar edge counts
-- statement:
--   For a finite simple graph with at least three vertices and a crossing-free drawing, the number of edges is at most three times the number of vertices minus six. This is the Euler-formula upper bound, written without subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_77901df4_aad7_410f_861f_76a2bd150be4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    G.edgeFinset.card + 6 <= 3 * Fintype.card V := by
  sorry
