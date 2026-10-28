-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_face_census
-- name    : WilliamsonShmoys.planar_drawingOn_face_census
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:28:16.442333+00:00
-- url     : https://prove2.me/theorems/a9e96261-9ace-47ab-bd06-587908bd3615
-- title:
--   Face census for a connected planar drawing
-- statement:
--   For a connected graph with at least three vertices and a crossing-free drawing, there is a finite face count and a length for each face such that Euler’s formula holds, the face lengths sum to twice the number of edges, and every face has length at least three. The independent proof route is to extract the cyclic edge order at each vertex from the arcs, define face walks, apply Euler’s formula, and handle bridges in the face-length lower bound using simplicity, connectedness, and the vertex-count hypothesis. This isolates the main topological work removed from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_face_census
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, ∃ degree : Fin f → ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      (∑ i : Fin f, degree i) = 2 * K.edgeSet.ncard ∧
      ∀ i, 3 ≤ degree i := by sorry
