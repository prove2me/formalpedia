-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
-- name    : WilliamsonShmoys.subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:46.065008+00:00
-- url     : https://prove2.me/theorems/fab29bd8-41cd-42d7-b2c9-eca06c4e663e
-- title:
--   Subgraphs have no more edges
-- statement:
--   If G is a subgraph of H on a finite vertex type, its edge finset has cardinality at most that of H, without a vertex-count restriction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edgeFinset_card_mono__p2m_0c1d2833_de32_49c5_aebf_88ae0a9260a2_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hsub : G ≤ H) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  sorry
