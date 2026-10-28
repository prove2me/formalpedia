-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count_v2
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T02:19:02.518381+00:00
-- url     : https://prove2.me/theorems/82a5a06c-b5ed-4489-aac1-a956691f8099
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A finite connected graph with the specified crossing-free drawing has a natural face count satisfying Euler’s equation. This removes the face-count existence and Euler-equation portion of the parent. A proof can formalize the plane-graph Euler argument by deleting cycle edges and tracking the face count, with the tree case as the base case. The statement includes connected trees and does not require the parent’s lower bound of three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
