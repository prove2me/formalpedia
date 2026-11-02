-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a1
-- name    : WilliamsonShmoys.finite_planar_supergraph_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T11:38:22.574301+00:00
-- url     : https://prove2.me/theorems/1d650f2f-e16d-460f-8b2f-a4541a6f63d7
-- title:
--   Finite maximal supergraph principle
-- statement:
--   For any predicate on simple graphs over a finite linearly ordered vertex type, every graph satisfying the predicate has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, H ≤ L → P L → L = K := by sorry
