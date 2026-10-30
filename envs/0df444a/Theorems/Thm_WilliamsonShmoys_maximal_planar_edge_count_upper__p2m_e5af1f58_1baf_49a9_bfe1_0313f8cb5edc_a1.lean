-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:14:20.914444+00:00
-- url     : https://prove2.me/theorems/4994fa52-8694-420c-b1ad-06ee126d888c
-- title:
--   Upper edge bound for a finite simple planar graph
-- statement:
--   Any finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_upper__p2m_e5af1f58_1baf_49a9_bfe1_0313f8cb5edc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
