-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edgeFinset_card_mono__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- name    : WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:09:57.550066+00:00
-- url     : https://prove2.me/theorems/fab17bec-6808-49d8-bd57-a5e0edf901e3
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   If one finite simple graph’s adjacencies are included in another’s on the same vertex type, its edgeFinset has no larger cardinality. This separates the elementary finite-set step from the planar arguments and lets the parent transfer the connected supergraph’s bound to the original graph. A proof maps each unordered edge of G to the same unordered edge of H and uses injectivity/cardinality monotonicity. No positivity assumption is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_8eefeb5d_6bb8_407d_b469_57becc19650a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : ∀ u v, G.Adj u v → H.Adj u v) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      letI : DecidableRel H.Adj := Classical.decRel H.Adj;
      G.edgeFinset.card <= H.edgeFinset.card) := by sorry
