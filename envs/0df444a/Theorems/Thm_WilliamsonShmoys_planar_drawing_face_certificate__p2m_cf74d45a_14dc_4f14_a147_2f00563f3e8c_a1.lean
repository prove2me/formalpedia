-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_certificate__p2m_cf74d45a_14dc_4f14_a147_2f00563f3e8c_a1
-- name    : WilliamsonShmoys.planar_drawing_face_certificate__p2m_cf74d45a_14dc_4f14_a147_2f00563f3e8c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:04.297959+00:00
-- url     : https://prove2.me/theorems/426c7029-5872-47cb-8c49-aeaec1cc7a04
-- title:
--   Finite face certificate for a connected planar drawing
-- statement:
--   Construct a finite type of faces and assign each face a natural-number boundary length. Prove Euler’s equation, that the sum of all face boundary lengths counts each edge side once, and that every face boundary has length at least three. The parent obtains its inequality by summing the per-face lower bounds and using the total-length identity; its Euler equality is supplied directly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_certificate__p2m_cf74d45a_14dc_4f14_a147_2f00563f3e8c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hV : 3 <= Fintype.card V) :
    exists (F : Type) (_ : Fintype F) (length : F → Nat),
      Fintype.card V + Fintype.card F = M.edgeSet.ncard + 2 /\
      (∑ f : F, length f) = 2 * M.edgeSet.ncard /\
      (∀ f : F, 3 <= length f) := by sorry
