-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_member_of_finite_family__p2m_2d1306cb_8fa9_487e_8a52_473fb2bb2b8b_a1
-- name    : WilliamsonShmoys.exists_maximal_member_of_finite_family__p2m_2d1306cb_8fa9_487e_8a52_473fb2bb2b8b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:59.97961+00:00
-- url     : https://prove2.me/theorems/db9babbd-2c96-4852-9165-0e1863c25a08
-- title:
--   A finite family of supergraphs has a maximal member
-- statement:
--   In any predicate-defined family of finite simple graphs that contains H, there is a member L containing H such that every family member extending L is also below L.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_member_of_finite_family__p2m_2d1306cb_8fa9_487e_8a52_473fb2bb2b8b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ L : SimpleGraph V,
      H ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M ≤ L := by sorry
