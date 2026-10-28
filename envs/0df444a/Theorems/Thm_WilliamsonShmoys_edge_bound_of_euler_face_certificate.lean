-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_certificate
-- name    : WilliamsonShmoys.edge_bound_of_euler_face_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:58:27.291983+00:00
-- url     : https://prove2.me/theorems/e8e8737b-da2f-4360-a681-a4666de1e69e
-- title:
--   Edge bound from Euler and face counts
-- statement:
--   If a finite simple graph is a subgraph of another graph whose vertex count, edge count, and face count satisfy Euler’s equation and the triangular face-incidence bound, then the original graph has at most three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_bound_of_euler_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hFaces : 3 * f ≤ 2 * K.edgeSet.ncard) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
