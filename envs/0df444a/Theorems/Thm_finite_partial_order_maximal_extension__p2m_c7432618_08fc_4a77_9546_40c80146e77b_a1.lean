-- Prove2me | Theorems.Thm_finite_partial_order_maximal_extension__p2m_c7432618_08fc_4a77_9546_40c80146e77b_a1
-- name    : finite_partial_order_maximal_extension__p2m_c7432618_08fc_4a77_9546_40c80146e77b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:30:28.040798+00:00
-- url     : https://prove2.me/theorems/6fc598a7-ba54-46fc-a7f8-59047eebe9e5
-- title:
--   Maximal predicate extension in a finite partial order
-- statement:
--   In a finite partially ordered type, every element satisfying a predicate has an extension satisfying that predicate that is maximal among predicate-satisfying elements above it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_partial_order_maximal_extension__p2m_c7432618_08fc_4a77_9546_40c80146e77b_a1
    {α : Type} [Finite α] [PartialOrder α]
    (P : α → Prop) (x : α) (hPx : P x) :
    ∃ y : α, x ≤ y ∧ P y ∧
      ∀ z : α, y ≤ z → P z → z = y := by
  sorry
