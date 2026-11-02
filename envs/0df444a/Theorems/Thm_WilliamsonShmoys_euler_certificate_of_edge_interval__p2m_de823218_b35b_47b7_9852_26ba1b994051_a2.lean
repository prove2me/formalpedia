-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_certificate_of_edge_interval__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
-- name    : WilliamsonShmoys.euler_certificate_of_edge_interval__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:07:31.242083+00:00
-- url     : https://prove2.me/theorems/6bc6eb7d-e3a6-428d-ac72-aab2e84f34c0
-- title:
--   Produce the Euler-style arithmetic certificate
-- statement:
--   For n ≥ 3 and n−2 ≤ m ≤ 3n−6, choose a natural f satisfying n+f=m+2 and 3f≤2m.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_certificate_of_edge_interval__p2m_de823218_b35b_47b7_9852_26ba1b994051_a2
    (n m : ℕ) (hn : 3 ≤ n) (hlower : n - 2 ≤ m) (hupper : m ≤ 3 * n - 6) :
    ∃ f : ℕ, n + f = m + 2 ∧ 3 * f ≤ 2 * m := by sorry
