-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_certificate_edge_bound__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
-- name    : WilliamsonShmoys.euler_certificate_edge_bound__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:06:36.113337+00:00
-- url     : https://prove2.me/theorems/95aabdf4-ee5d-4887-ac69-11be9f3010bb
-- title:
--   Euler certificate implies the planar edge bound
-- statement:
--   For natural numbers `n`, `m`, `m'`, and `f`, the stated Euler equation and face-degree inequality imply `m' ≤ 3 * n - 6`; the bound `m ≤ m'` then gives the desired edge bound. The hypothesis `3 ≤ n` ensures the natural-number subtraction has the intended value. This is a linear arithmetic step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.euler_certificate_edge_bound__p2m_10555cd3_1e32_4780_a0c9_e859a324fd87_a1
    (n m m' f : Nat)
    (hn : 3 ≤ n)
    (hcert : m ≤ m' ∧ n + f = m' + 2 ∧ 3 * f ≤ 2 * m') :
    m ≤ 3 * n - 6 := by sorry
