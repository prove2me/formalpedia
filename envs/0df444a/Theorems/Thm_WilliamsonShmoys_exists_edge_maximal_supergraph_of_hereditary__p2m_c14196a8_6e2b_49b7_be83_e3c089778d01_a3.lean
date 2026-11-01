-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_supergraph_of_hereditary__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
-- name    : WilliamsonShmoys.exists_edge_maximal_supergraph_of_hereditary__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:42:44.733707+00:00
-- url     : https://prove2.me/theorems/39b66288-b9dd-430f-8b7b-434cfc203be4
-- title:
--   Finite hereditary graph properties have maximal extensions
-- statement:
--   On a finite vertex type, any edge-subgraph-closed graph property has an edge-maximal extension containing any given graph that satisfies the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_supergraph_of_hereditary__p2m_c14196a8_6e2b_49b7_be83_e3c089778d01_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (P : SimpleGraph V → Prop)
    (hdown : ∀ (A B : SimpleGraph V) (dA : DecidableRel A.Adj) (dB : DecidableRel B.Adj),
      (letI : DecidableRel A.Adj := dA
       letI : DecidableRel B.Adj := dB
       A.edgeFinset ⊆ B.edgeFinset) → P B → P A)
    (hP : P K) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      P H ∧
      ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        P G →
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel G.Adj := dG
         H.edgeFinset ⊆ G.edgeFinset → H.edgeFinset = G.edgeFinset) := by sorry
