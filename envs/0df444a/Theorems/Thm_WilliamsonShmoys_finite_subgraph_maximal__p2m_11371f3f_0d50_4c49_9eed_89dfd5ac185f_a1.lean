-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_subgraph_maximal__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
-- name    : WilliamsonShmoys.finite_subgraph_maximal__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:34.834768+00:00
-- url     : https://prove2.me/theorems/27b626d1-ff59-4343-9378-f6bc9a2f271e
-- title:
--   Finite maximal graph in a hereditary class
-- statement:
--   For a finite vertex type, any downward-closed class of simple graphs containing Z has a member H that contains Z, has at least as many edges as Z, and has no proper supergraph in the class. Finiteness permits maximizing edge count among the candidate graphs; a proper extension would contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_subgraph_maximal__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1 {V : Type} [Fintype V] [LinearOrder V] (Z : SimpleGraph V) (P : SimpleGraph V → Prop) (hZ : P Z) (hdown : ∀ {G H : SimpleGraph V}, (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) → P H → P G) : ∃ H : SimpleGraph V, (∀ ⦃u v : V⦄, Z.Adj u v → H.Adj u v) ∧ Z.edgeSet.ncard ≤ H.edgeSet.ncard ∧ P H ∧ ∀ K : SimpleGraph V, (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) → P K → K = H := by sorry
