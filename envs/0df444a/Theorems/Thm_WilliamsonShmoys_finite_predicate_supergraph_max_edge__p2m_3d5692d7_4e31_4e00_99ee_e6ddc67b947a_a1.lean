-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_predicate_supergraph_max_edge__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
-- name    : WilliamsonShmoys.finite_predicate_supergraph_max_edge__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:12.53886+00:00
-- url     : https://prove2.me/theorems/870a0314-6146-4fcb-bf6c-41a14a5f6fed
-- title:
--   Maximum edge count among finite predicate supergraphs
-- statement:
--   There is a P-satisfying supergraph of H whose edge count is at least that of every P-satisfying supergraph of H. This removes the finite candidate-selection and maximization work from the parent; maximize edge cardinality over the finite family of eligible graphs. The family is nonempty because it contains H, including when the vertex type is empty. The remaining core obligation is to formalize finiteness of the candidate family and the maximum argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_predicate_supergraph_max_edge__p2m_3d5692d7_4e31_4e00_99ee_e6ddc67b947a_a1 {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hP : P H) (hereditary : ∀ ⦃G K : SimpleGraph V⦄, G ≤ K → P K → P G) : ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧ ∀ L : SimpleGraph V, H ≤ L → P L → L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
