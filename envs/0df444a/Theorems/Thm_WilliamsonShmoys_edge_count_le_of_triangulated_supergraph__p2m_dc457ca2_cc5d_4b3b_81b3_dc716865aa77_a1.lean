-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_le_of_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
-- name    : WilliamsonShmoys.edge_count_le_of_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:45.092108+00:00
-- url     : https://prove2.me/theorems/953baa0d-14af-476a-8eda-7b232dad3e8a
-- title:
--   Edge count is bounded by a triangulated supergraph
-- statement:
--   If the edges of a finite simple graph are included among those of a graph on the same vertices whose edge count is exactly 3|V|−6, then the first graph has at most 3|V|−6 edges. The exact cardinality hypothesis handles the subtraction boundary directly; the parent supplies at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_count_le_of_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (dG : DecidableRel G.Adj) (dH : DecidableRel H.Adj)
    (hsub : (letI : DecidableRel G.Adj := dG; letI : DecidableRel H.Adj := dH; G.edgeFinset ⊆ H.edgeFinset))
    (hcard : (letI : DecidableRel H.Adj := dH; H.edgeFinset.card = 3 * Fintype.card V - 6)) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
