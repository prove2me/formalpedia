-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:44:08.821991+00:00
-- url     : https://prove2.me/theorems/aa9babaa-2b75-4231-a744-e17b7c0bb36c
-- title:
--   Euler upper bound for a finite planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3n−6 edges. This removes the universal planar edge-bound step from the parent. A proof route is to connect components and triangulate a planar embedding, then combine Euler’s formula with the fact that each triangular face contributes three boundary incidences while each edge is incident to at most two faces. The exact bound includes disconnected graphs and the n=3 boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper__p2m_116aa790_44aa_4b8f_ae9f_0f35011c7378_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
