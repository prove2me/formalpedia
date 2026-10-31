-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_24784cbb_b8f6_4e91_b5ba_b51ad6a651ca_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_24784cbb_b8f6_4e91_b5ba_b51ad6a651ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:28.726546+00:00
-- url     : https://prove2.me/theorems/5018a7ca-685e-45bb-8182-32c4edb5ec6b
-- title:
--   Finite maximal supergraph for an arbitrary graph property
-- statement:
--   For any property of graphs on a finite vertex type, every graph satisfying that property has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_24784cbb_b8f6_4e91_b5ba_b51ad6a651ca_a1 {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (X : SimpleGraph V) (hX : P X) : ∃ Y : SimpleGraph V, X ≤ Y ∧ P Y ∧ ∀ Z : SimpleGraph V, Y ≤ Z → P Z → Y = Z := by sorry
