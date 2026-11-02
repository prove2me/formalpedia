-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edgeFinset_card__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
-- name    : WilliamsonShmoys.exists_max_edgeFinset_card__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:42.655838+00:00
-- url     : https://prove2.me/theorems/7f44c791-65bd-4366-882a-44fc4e2816b3
-- title:
--   A bounded class of supergraphs has a maximum edge count
-- statement:
--   For a predicate P on graphs that holds of K, if all graphs satisfying P have edge count at most N, then some P-graph containing K maximizes edge count among all P-graphs containing K. The result abstracts the finite maximization away from planarity. A proof route is to form the attainable cardinalities in the finite range from 0 to N, choose a largest attainable cardinality, and retain a graph witnessing it; edge-set inclusion ensures the witness class includes K and the maximization compares every qualifying supergraph. The parent supplies P as drawable planarity and the uniform bound from the first child. The remaining work in this child is formalizing the finite range and witness selection with the required decidable edge-relation instances.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_edgeFinset_card__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) [DecidableRel K.Adj] (P : SimpleGraph V → Prop) (hK : P K) (N : Nat) (hbound : ∀ (G : SimpleGraph V) [DecidableRel G.Adj], P G → G.edgeFinset.card ≤ N) : ∃ L : SimpleGraph V, P L ∧ ∃ dL : DecidableRel L.Adj, letI : DecidableRel L.Adj := dL; K.edgeFinset ⊆ L.edgeFinset ∧ ∀ (M : SimpleGraph V) [DecidableRel M.Adj], P M → L.edgeFinset ⊆ M.edgeFinset → M.edgeFinset.card ≤ L.edgeFinset.card := by sorry
