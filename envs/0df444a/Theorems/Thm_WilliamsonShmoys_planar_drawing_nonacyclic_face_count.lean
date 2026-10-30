-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_nonacyclic_face_count
-- name    : WilliamsonShmoys.planar_drawing_nonacyclic_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:26:30.054+00:00
-- url     : https://prove2.me/theorems/f6d1941e-096c-42d9-a12f-4557d5ddf9e9
-- title:
--   Euler and face-side bounds from a cyclic planar drawing
-- statement:
--   For a finite connected simple graph with a cycle and the specified crossing-free drawing, the number of faces satisfies Euler’s equation and the sum of face-boundary lengths is twice the edge count, with every face boundary having length at least three. A proof route is to extract the cyclic order of incident arcs at each vertex, use it to define the face walks of the resulting plane rotation system, obtain Euler’s formula for a connected plane graph, and count edge sides. The cyclicity hypothesis excludes the tree case, whose face walk can have length two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_nonacyclic_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCyclic : ¬ G.IsAcyclic) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
