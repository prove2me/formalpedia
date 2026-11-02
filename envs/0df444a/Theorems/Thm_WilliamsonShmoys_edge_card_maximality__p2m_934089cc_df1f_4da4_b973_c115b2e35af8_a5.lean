-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
-- name    : WilliamsonShmoys.edge_card_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:28:11.050291+00:00
-- url     : https://prove2.me/theorems/a61d9a0f-7ed9-4df5-b989-3e94ccc47412
-- title:
--   Subgraph equality from edge counts
-- statement:
--   For finite edge sets, subgraph inclusion and a reverse inequality on edge counts imply equality of the simple graphs. A proof follows from inclusion of edge finsets and the fact that a strict inclusion of finite sets increases cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_card_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
    {V : Type} [Fintype V]
    {G L : SimpleGraph V} [Fintype G.edgeSet] [Fintype L.edgeSet]
    (hGL : G ≤ L)
    (hcard : L.edgeFinset.card ≤ G.edgeFinset.card) :
    L = G := by sorry
