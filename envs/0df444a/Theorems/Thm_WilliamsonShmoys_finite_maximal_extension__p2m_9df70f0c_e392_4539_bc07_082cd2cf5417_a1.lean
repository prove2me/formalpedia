-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension__p2m_9df70f0c_e392_4539_bc07_082cd2cf5417_a1
-- name    : WilliamsonShmoys.finite_maximal_extension__p2m_9df70f0c_e392_4539_bc07_082cd2cf5417_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:40:14.423148+00:00
-- url     : https://prove2.me/theorems/fb3a7c2c-7564-4d00-86e3-35e047099090
-- title:
--   Finite maximal extension for a predicate
-- statement:
--   In a finite partial order, every element satisfying a predicate lies below a predicate-satisfying element that is maximal among predicate-satisfying elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_extension__p2m_9df70f0c_e392_4539_bc07_082cd2cf5417_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop) {a : α} (ha : P a) :
    ∃ b, a ≤ b ∧ P b ∧ ∀ c, b ≤ c → P c → c ≤ b := by
  sorry
