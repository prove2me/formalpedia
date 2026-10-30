-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_maximal__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_finite_maximal__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:52:18.285657+00:00
-- url     : https://prove2.me/theorems/644d8d94-7b95-4a48-997e-d6c303d2401e
-- title:
--   A maximal member of a nonempty finite partially ordered family
-- statement:
--   Every nonempty predicate-defined subset of a finite partially ordered type contains an element maximal among the elements satisfying the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_finite_maximal__p2m_bed1e8e9_9063_4971_87d4_a573a94b3117_a1 {α : Type} [Fintype α] [PartialOrder α] (P : α → Prop) (hP : ∃ x, P x) : ∃ x, P x ∧ ∀ y, x ≤ y → P y → y = x := by sorry
