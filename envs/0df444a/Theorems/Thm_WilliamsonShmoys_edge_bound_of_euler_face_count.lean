-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_count
-- name    : WilliamsonShmoys.edge_bound_of_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:39:08.074644+00:00
-- url     : https://prove2.me/theorems/bf005e6c-d8e4-4588-847a-7d4e3907dd43
-- title:
--   Euler face equations imply the maximal planar edge count
-- statement:
--   Euler’s equation and the triangular face-edge incidence equation imply the exact edge-count identity by linear arithmetic. This separates the numeric calculation from the topological face-count argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_of_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hTri : 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
