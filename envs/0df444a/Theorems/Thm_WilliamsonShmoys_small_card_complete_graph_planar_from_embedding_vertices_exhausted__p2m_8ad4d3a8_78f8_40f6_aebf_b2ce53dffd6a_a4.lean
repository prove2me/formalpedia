-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_planar_from_embedding_vertices_exhausted__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- name    : WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_vertices_exhausted__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:10:42.462444+00:00
-- url     : https://prove2.me/theorems/5a25319e-2f30-4e9d-9bd4-58d1379a4466
-- title:
--   Every third vertex is an endpoint
-- statement:
--   For a finite linearly ordered type with fewer than three elements, any two distinct vertices exhaust the type. This supplies the parent’s interior-avoidance argument by reducing each vertex to one of the two edge endpoints. Prove it from the cardinality bound and distinctness of the chosen endpoints; the remaining geometry is handled by the segment child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_card_complete_graph_planar_from_embedding_vertices_exhausted__p2m_8ad4d3a8_78f8_40f6_aebf_b2ce53dffd6a_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (hsmall : Fintype.card V < 3) (u v : V) (huv : Not (u = v)) :
    forall w : V, Or (w = u) (w = v) := by
  sorry
