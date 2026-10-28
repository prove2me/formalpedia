-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_face_lengths
-- name    : WilliamsonShmoys.planar_drawingOn_face_lengths
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:38:28.355863+00:00
-- url     : https://prove2.me/theorems/cf2dd233-74fa-46c3-9c24-afbd1941f8c6
-- title:
--   Face boundary lengths for a planar drawing
-- statement:
--   For a connected simple planar drawing with at least three vertices, the facial boundary walks can be indexed by the Euler face count; their lengths sum to twice the number of edges, and each has length at least three. Bridges are counted twice in boundary walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_face_lengths
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V)
    (f : ℕ)
    (heuler : Fintype.card V + f = K.edgeSet.ncard + 2) :
    ∃ degree : Fin f → ℕ,
      (∑ i : Fin f, degree i) = 2 * K.edgeSet.ncard ∧
      ∀ i, 3 ≤ degree i := by sorry
