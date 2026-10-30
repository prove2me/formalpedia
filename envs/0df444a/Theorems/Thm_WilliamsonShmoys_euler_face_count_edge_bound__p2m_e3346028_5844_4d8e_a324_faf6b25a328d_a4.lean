-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_edge_bound__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- name    : WilliamsonShmoys.euler_face_count_edge_bound__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:21:38.508047+00:00
-- url     : https://prove2.me/theorems/5acd19c6-cc18-4ffe-a85a-2e01f10eba95
-- title:
--   Euler face counts imply the planar edge bound
-- statement:
--   Derive the target edge bound by natural-number arithmetic from Euler’s equation and the face-incidence inequality. This removes the arithmetic from the parent; the geometric face construction remains the first child’s obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_face_count_edge_bound__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
    {V : Type} [Fintype V]
    (M : SimpleGraph V)
    (F : Type) [Fintype F]
    (hEuler : Fintype.card V + Fintype.card F = M.edgeSet.ncard + 2)
    (hInc : 3 * Fintype.card F <= 2 * M.edgeSet.ncard) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
