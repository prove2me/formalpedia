-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_of_finite_subgraph_closed
-- name    : WilliamsonShmoys.exists_maximal_of_finite_subgraph_closed
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:11:24.667101+00:00
-- url     : https://prove2.me/theorems/3417d15c-cc27-40dd-8e97-fd2abb046274
-- title:
--   Maximal supergraph for a downward-closed property
-- statement:
--   For a finite vertex type, any graph satisfying a subgraph-closed property has a supergraph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_of_finite_subgraph_closed {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A) (G : SimpleGraph V) (hG : P G) : ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
