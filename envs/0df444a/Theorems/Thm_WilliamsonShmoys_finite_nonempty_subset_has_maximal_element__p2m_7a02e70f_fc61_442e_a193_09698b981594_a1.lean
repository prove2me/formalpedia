-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_nonempty_subset_has_maximal_element__p2m_7a02e70f_fc61_442e_a193_09698b981594_a1
-- name    : WilliamsonShmoys.finite_nonempty_subset_has_maximal_element__p2m_7a02e70f_fc61_442e_a193_09698b981594_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:54:42.39825+00:00
-- url     : https://prove2.me/theorems/7042164d-4f01-48a0-91a9-75044da78777
-- title:
--   Maximal element in a nonempty subset of a finite partial order
-- statement:
--   Every nonempty subset of a finite partially ordered type contains an element with no strictly larger element in that subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_nonempty_subset_has_maximal_element__p2m_7a02e70f_fc61_442e_a193_09698b981594_a1
    {α : Type} [Finite α] [PartialOrder α]
    (s : α → Prop)
    (hne : ∃ x, s x) :
    ∃ x, s x ∧ ∀ y, x ≤ y → s y → y = x := by sorry
