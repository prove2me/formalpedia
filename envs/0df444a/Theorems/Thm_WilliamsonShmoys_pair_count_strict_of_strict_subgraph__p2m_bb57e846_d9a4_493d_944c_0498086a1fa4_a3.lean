-- Prove2me | Theorems.Thm_WilliamsonShmoys_pair_count_strict_of_strict_subgraph__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
-- name    : WilliamsonShmoys.pair_count_strict_of_strict_subgraph__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:02:03.912996+00:00
-- url     : https://prove2.me/theorems/0677a47c-a8c3-4f32-b2c2-f8630bed9f90
-- title:
--   A strict graph extension increases adjacent-pair count
-- statement:
--   If L is a subgraph of M and M is not a subgraph of L, inclusion of adjacent ordered-pair subtypes is strict, so their finite cardinalities are strictly ordered.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.pair_count_strict_of_strict_subgraph__p2m_bb57e846_d9a4_493d_944c_0498086a1fa4_a3 {V : Type} [Fintype V] [LinearOrder V] (L M : SimpleGraph V) (hLM : L ≤ M) (hML : ¬ M ≤ L) : Nat.card {p : V × V // L.Adj p.1 p.2} < Nat.card {p : V × V // M.Adj p.1 p.2} := by sorry
