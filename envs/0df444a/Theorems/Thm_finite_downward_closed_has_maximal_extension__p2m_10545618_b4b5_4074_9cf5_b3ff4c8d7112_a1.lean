-- Prove2me | Theorems.Thm_finite_downward_closed_has_maximal_extension__p2m_10545618_b4b5_4074_9cf5_b3ff4c8d7112_a1
-- name    : finite_downward_closed_has_maximal_extension__p2m_10545618_b4b5_4074_9cf5_b3ff4c8d7112_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:44:22.934228+00:00
-- url     : https://prove2.me/theorems/e2dae458-2b4e-415b-986d-dc048fe9b31c
-- title:
--   Finite partially ordered sets have maximal extensions for downward-closed properties
-- statement:
--   In a finite partially ordered type, any element satisfying a downward-closed property lies below an element satisfying that property that is maximal among all such elements.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_downward_closed_has_maximal_extension__p2m_10545618_b4b5_4074_9cf5_b3ff4c8d7112_a1
    {α : Type} [Fintype α] [PartialOrder α]
    (P : α → Prop)
    (hdown : ∀ {x y : α}, x ≤ y → P y → P x)
    (a : α) (ha : P a) :
    ∃ b : α, a ≤ b ∧ P b ∧ ∀ c : α, b ≤ c → P c → c ≤ b := by
  sorry
