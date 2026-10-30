-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_arithmetic__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- name    : WilliamsonShmoys.face_data_arithmetic__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T05:53:50.120112+00:00
-- url     : https://prove2.me/theorems/811751c4-7b8e-4969-a6e6-f904ed10f9d9
-- title:
--   Construct face counts and lengths from edge bounds
-- statement:
--   Given n ≥ 3, n ≤ m + 2, and m ≤ 3n − 6, construct a finite set of m + 2 − n faces and assign each a natural length at least three, with total length 2m.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.face_data_arithmetic__p2m_58a549ee_4768_4664_9403_907071b96f48_a4 (n m : Nat) (hn : 3 ≤ n) (hlow : n ≤ m + 2) (hupp : m ≤ 3 * n - 6) : ∃ (F : Type) (inst : Fintype F) (length : F → Nat), n + @Fintype.card F inst = m + 2 ∧ (∀ f : F, 3 ≤ length f) ∧ (letI : Fintype F := inst; (∑ f : F, length f) = 2 * m) := by sorry
