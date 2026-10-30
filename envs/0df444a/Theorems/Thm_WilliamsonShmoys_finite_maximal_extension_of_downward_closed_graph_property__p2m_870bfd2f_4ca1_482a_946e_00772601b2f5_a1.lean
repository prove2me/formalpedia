-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_downward_closed_graph_property__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
-- name    : WilliamsonShmoys.finite_maximal_extension_of_downward_closed_graph_property__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:31:08.076324+00:00
-- url     : https://prove2.me/theorems/80773985-9e66-4318-87cf-d5dc60b79518
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For any finite vertex type, every graph satisfying a downward-closed property has a supergraph satisfying that property that is maximal among such supergraphs. The independent proof route is to maximize the number of edges among the finite collection of eligible supergraphs, then use strict edge inclusion to contradict maximality of the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension_of_downward_closed_graph_property__p2m_870bfd2f_4ca1_482a_946e_00772601b2f5_a1
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (Q : SimpleGraph V → Prop)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → Q H → Q G)
    (hM : Q M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ Q N ∧
      ∀ P : SimpleGraph V, N ≤ P → Q P → P = N := by
  sorry
