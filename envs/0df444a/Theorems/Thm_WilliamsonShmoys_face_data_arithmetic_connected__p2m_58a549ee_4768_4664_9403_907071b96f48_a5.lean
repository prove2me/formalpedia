-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_arithmetic_connected__p2m_58a549ee_4768_4664_9403_907071b96f48_a5
-- name    : WilliamsonShmoys.face_data_arithmetic_connected__p2m_58a549ee_4768_4664_9403_907071b96f48_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:04:59.640993+00:00
-- url     : https://prove2.me/theorems/a708db1e-fc25-4ef8-91b9-16766c2f93f0
-- title:
--   Construct face counts and lengths from connected and planar edge bounds
-- statement:
--   If `n ≥ 3`, connectedness supplies `n ≤ m + 1`, and the planar edge bound gives `m ≤ 3n − 6`; then a finite set of `m + 2 − n` faces can be assigned lengths at least three summing to `2m`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.face_data_arithmetic_connected__p2m_58a549ee_4768_4664_9403_907071b96f48_a5 (n m : Nat) (hn : 3 ≤ n) (hlow : n ≤ m + 1) (hupp : m ≤ 3 * n - 6) : ∃ (F : Type) (inst : Fintype F) (length : F → Nat), n + @Fintype.card F inst = m + 2 ∧ (∀ f : F, 3 ≤ length f) ∧ (letI : Fintype F := inst; (∑ f : F, length f) = 2 * m) := by sorry
