-- Prove2me | Theorems.Thm_WilliamsonShmoys_ncard_lt_of_strict_le_20261026
-- name    : WilliamsonShmoys.ncard_lt_of_strict_le_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:14:42.04912+00:00
-- url     : https://prove2.me/theorems/4c4f9373-d271-4b0d-ac8d-347a94fe0795
-- title:
--   Proper graph extension increases edge-set cardinality
-- statement:
--   For finite V, graph inclusion gives edge-set inclusion; if the graphs differ, that inclusion is proper, so the finite edge-set cardinality strictly increases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.ncard_lt_of_strict_le_20261026
    {V : Type} [Fintype V]
    (M N : SimpleGraph V)
    (hMN : M ≤ N)
    (hne : N ≠ M) :
    M.edgeSet.ncard < N.edgeSet.ncard := by sorry
