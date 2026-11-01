-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_downward_property__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_downward_property__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:59:33.598339+00:00
-- url     : https://prove2.me/theorems/325484a2-4342-4d52-8a91-7f2954e17230
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite ordered vertex type, if a graph property holds for H and is preserved when passing to subgraphs, then H has a property-preserving supergraph maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_downward_property__p2m_dbde89e8_c849_4801_a07f_e697f1afc8ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P H)
    (hdown : ∀ ⦃G G' : SimpleGraph V⦄, G ≤ G' → P G' → P G) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K := by sorry
