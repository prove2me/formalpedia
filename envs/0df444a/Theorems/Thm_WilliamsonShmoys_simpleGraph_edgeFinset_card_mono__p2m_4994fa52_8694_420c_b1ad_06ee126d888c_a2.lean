-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeFinset_card_mono__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- name    : WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:22:39.913853+00:00
-- url     : https://prove2.me/theorems/60dd97e1-0d8f-47a3-98dd-ceca4561ed1e
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite vertex types, graph inclusion implies that the smaller graph has no more edges than the larger graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_edgeFinset_card_mono__p2m_4994fa52_8694_420c_b1ad_06ee126d888c_a2
    {V : Type} [Fintype V]
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hGH : G ≤ H) :
    G.edgeFinset.card ≤ H.edgeFinset.card := by
  sorry
