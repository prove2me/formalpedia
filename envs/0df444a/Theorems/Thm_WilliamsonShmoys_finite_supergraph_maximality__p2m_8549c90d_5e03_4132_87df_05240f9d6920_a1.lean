-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1
-- name    : WilliamsonShmoys.finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:38:34.775989+00:00
-- url     : https://prove2.me/theorems/04775818-5d64-4bc0-9dc9-203695626bbe
-- title:
--   Finite maximality among property-bearing graph supergraphs
-- statement:
--   For any predicate P on simple graphs over a finite vertex type, every graph H satisfying P has a P-supergraph that is maximal among P-supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_supergraph_maximality__p2m_8549c90d_5e03_4132_87df_05240f9d6920_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) : ∃ J : SimpleGraph V, H ≤ J ∧ P J ∧ (∀ K : SimpleGraph V, J ≤ K → P K → K ≤ J) := by sorry
