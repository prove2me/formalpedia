-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_certificate_of_drawing
-- name    : WilliamsonShmoys.planar_triangulation_certificate_of_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T17:02:47.68198+00:00
-- url     : https://prove2.me/theorems/1bb3a12b-18f2-4a01-afbb-d45898a830ec
-- title:
--   Triangulation certificate from a planar drawing
-- statement:
--   Every connected graph with at least three vertices and the supplied crossing-free drawing has a same-vertex simple graph extension with Euler and triangular-face incidence counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationCertificate

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_certificate_of_drawing
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) : Nonempty (PlanarTriangulationCertificate G) := by
  sorry
