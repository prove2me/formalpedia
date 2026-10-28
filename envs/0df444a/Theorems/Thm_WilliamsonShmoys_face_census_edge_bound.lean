-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_census_edge_bound
-- name    : WilliamsonShmoys.face_census_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:28:59.226122+00:00
-- url     : https://prove2.me/theorems/6a4112de-d1e4-49bb-865d-d5342be5ec92
-- title:
--   Edge bound from a face census
-- statement:
--   A finite face census satisfying Euler’s equation and the double-count of edge sides implies the planar edge bound. Sum the pointwise lower bound on face lengths to obtain `3 * f ≤ 2 * m`, then combine it with `n + f = m + 2` and `n ≥ 3` by natural-number arithmetic. This child is independent of graph drawing geometry and removes only the routine counting and arithmetic from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.face_census_edge_bound
    (n m f : ℕ)
    (degree : Fin f → ℕ)
    (hn : 3 ≤ n)
    (hEuler : n + f = m + 2)
    (hDegreeSum : (∑ i : Fin f, degree i) = 2 * m)
    (hFaceDegree : ∀ i, 3 ≤ degree i) :
    m ≤ 3 * n - 6 := by sorry
