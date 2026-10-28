-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_face_system_edge_bound
-- name    : WilliamsonShmoys.triangular_face_system_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:03:14.00308+00:00
-- url     : https://prove2.me/theorems/534632ab-1d3b-4820-8cbf-75a8eb993d6a
-- title:
--   Triangular face data imply the Euler edge bound
-- statement:
--   For a finite simple graph, triangular face data in which every graph edge belongs to exactly two faces and Euler’s equation holds imply the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.triangular_face_system_edge_bound
    {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (hfaces : WilliamsonShmoys.HasTriangularPlaneFaceSystem H) :
    H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
