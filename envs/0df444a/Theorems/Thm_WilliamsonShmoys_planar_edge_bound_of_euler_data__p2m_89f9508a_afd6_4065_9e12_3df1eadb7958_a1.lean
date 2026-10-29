-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_of_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
-- name    : WilliamsonShmoys.planar_edge_bound_of_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:29:46.9562+00:00
-- url     : https://prove2.me/theorems/eba3db44-e551-47a9-a4d5-30ee49bd8f17
-- title:
--   Planar edge bound from Euler data
-- statement:
--   If n ≥ 3, n + f = m + 2, and 3f ≤ 2m, then m ≤ 3n − 6. Substituting the Euler equation into the face-count inequality gives the result; this is a linear natural-number arithmetic obligation. The boundary n = 3 is included, and hn ensures the truncated subtraction on the conclusion has the intended value.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_edge_bound_of_euler_data__p2m_89f9508a_afd6_4065_9e12_3df1eadb7958_a1
    (n m f : ℕ) (hn : 3 ≤ n) (hEuler : n + f = m + 2)
    (hFaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
