-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_face_count_forces_edge_count
-- name    : WilliamsonShmoys.triangulation_face_count_forces_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:09:18.227726+00:00
-- url     : https://prove2.me/theorems/02bc4a07-fcc7-4185-97ce-d8fc483c1670
-- title:
--   Triangular face counts determine the edge count
-- statement:
--   For finite triangular face data, Euler’s relation and the fact that every edge is incident to two face sides imply that the vertex and edge counts satisfy the maximal planar edge equation. This is independent finite counting; substitute the constant face length into the sum and use linear arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_face_count_forces_edge_count
    {n e : ℕ} {F : Type} [Fintype F]
    (boundaryLength : F → ℕ)
    (hEuler : n + Fintype.card F = e + 2)
    (hIncidence : (∑ f : F, boundaryLength f) = 2 * e)
    (hTriangle : ∀ f, boundaryLength f = 3) :
    3 * n = e + 6 := by sorry
