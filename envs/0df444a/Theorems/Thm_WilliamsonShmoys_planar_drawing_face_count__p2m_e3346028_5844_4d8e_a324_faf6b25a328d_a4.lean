-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:27.684986+00:00
-- url     : https://prove2.me/theorems/cf74d45a-14dc-4f14-a147-2f00563f3e8c
-- title:
--   A planar drawing yields Euler face counts
-- statement:
--   Construct a finite face type for the connected planar drawing whose cardinality satisfies Euler’s equation and whose face incidences obey the planar lower bound. The drawing provides a plane embedding; simplicity and the vertex-count hypothesis rule out facial boundary walks of length below three. The proof route is to construct face walks from the embedding, prove Euler’s equation, and count the two sides of every edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_e3346028_5844_4d8e_a324_faf6b25a328d_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 <= Fintype.card V) :
    exists (F : Type) (_ : Fintype F),
      Fintype.card V + Fintype.card F = M.edgeSet.ncard + 2 /\
      3 * Fintype.card F <= 2 * M.edgeSet.ncard := by sorry
