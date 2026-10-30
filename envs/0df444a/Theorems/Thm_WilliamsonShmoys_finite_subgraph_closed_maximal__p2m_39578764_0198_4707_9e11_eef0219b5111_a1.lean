-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_subgraph_closed_maximal__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
-- name    : WilliamsonShmoys.finite_subgraph_closed_maximal__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:27:34.605992+00:00
-- url     : https://prove2.me/theorems/f1350172-eccd-4d30-8af3-b1246339198a
-- title:
--   Maximal extension for a subgraph-closed property on a finite vertex type
-- statement:
--   For a finite vertex type, any graph satisfying a subgraph-closed property is contained in a graph maximal among graphs with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_subgraph_closed_maximal__p2m_39578764_0198_4707_9e11_eef0219b5111_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hsub : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by
  sorry
