-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_strict_of_lt__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:56:41.443568+00:00
-- url     : https://prove2.me/theorems/ed099cc8-d312-4292-a691-251c89569ef3
-- title:
--   Proper graph extension strictly increases edge count
-- statement:
--   On a finite vertex type, a proper simple-graph extension has strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_4f8ddee9_6bbc_42a8_909b_77c7ff633307_a1
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (h : G < H) :
    G.edgeSet.ncard < H.edgeSet.ncard := by sorry
