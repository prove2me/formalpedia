-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_certificate_edge_bound
-- name    : WilliamsonShmoys.planar_euler_certificate_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:37:38.836539+00:00
-- url     : https://prove2.me/theorems/38556140-0793-40eb-bd18-69c44340320e
-- title:
--   Edge bound from an Euler face certificate
-- statement:
--   If n ≥ 3 and the face count satisfies Euler’s equation together with 3f ≤ 2m, then m ≤ 3n − 6. This removes all remaining arithmetic from the parent. An independent proof route is linear arithmetic after converting the face inequality and Euler equation to integer inequalities; hn also ensures the natural-number subtraction in the conclusion does not underflow. The statement preserves the strict small-graph boundary through hn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_euler_certificate_edge_bound
    (n m f : Nat)
    (hn : 3 ≤ n)
    (heuler : (n : Int) - (m : Int) + (f : Int) = 2)
    (hfaces : 3 * f ≤ 2 * m) :
    m ≤ 3 * n - 6 := by sorry
