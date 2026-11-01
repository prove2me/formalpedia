-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
-- name    : WilliamsonShmoys.exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:18:48.617345+00:00
-- url     : https://prove2.me/theorems/98a63ac8-44e0-43f8-b521-d35550a2ef7b
-- title:
--   Finite maximal edge superset
-- statement:
--   Among the graphs satisfying a predicate and extending H by edges, there is one maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_edge_superset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset ∧
      P K ∧
      ∀ G : SimpleGraph V, K.edgeFinset ⊆ G.edgeFinset → P G → G = K := by sorry
