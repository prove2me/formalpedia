-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_supergraph_maximal_edgeFinset_cardinality__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
-- name    : WilliamsonShmoys.exists_supergraph_maximal_edgeFinset_cardinality__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:11.3738+00:00
-- url     : https://prove2.me/theorems/e7855619-1258-431b-bded-366dc5c9128c
-- title:
--   A valid supergraph with maximal edge count
-- statement:
--   Among the P-valid supergraphs of G, there is one whose finite edge set has maximum cardinality. The finiteness witnesses make explicit the instances needed to count each graph’s edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
open SimpleGraph

theorem WilliamsonShmoys.exists_supergraph_maximal_edgeFinset_cardinality__p2m_2212fb5a_3b8b_4ff4_b66b_e1a858c8b349_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∃ (hHfin : Fintype H.edgeSet), ∀ K : SimpleGraph V, G ≤ K → P K → ∀ (hKfin : Fintype K.edgeSet), @Fintype.card K.edgeSet hKfin ≤ @Fintype.card H.edgeSet hHfin := by sorry
