-- Prove2me | Theorems.Thm_WilliamsonShmoys_max_ncard_extension__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
-- name    : WilliamsonShmoys.max_ncard_extension__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:10:30.99456+00:00
-- url     : https://prove2.me/theorems/20a32935-bd00-4e75-852d-41d0b6d09a68
-- title:
--   A graph family contains a member with greatest edge count
-- statement:
--   For any nonempty family of simple graphs on a finite vertex type, some member has at least as many edges as every other member.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.max_ncard_extension__p2m_97b00d21_85c3_4456_b639_3b0e033871b5_a3
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    ∃ L, P L ∧ ∀ M, P M → M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
