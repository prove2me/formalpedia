-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_strict_of_lt__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
-- name    : WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:42.73899+00:00
-- url     : https://prove2.me/theorems/66642bba-bd25-4a4a-ba81-e3f90b00228d
-- title:
--   Strict graph inclusion increases edge count
-- statement:
--   For graphs on a finite vertex type, proper inclusion strictly increases the cardinality of the edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_strict_of_lt__p2m_8fdb3697_68d3_4381_90c9_e2e8988aff76_a2
    {V : Type} [Fintype V] (G N : SimpleGraph V)
    (hGN : G ≤ N) (hne : G ≠ N) :
    Set.ncard G.edgeSet < Set.ncard N.edgeSet := by sorry
