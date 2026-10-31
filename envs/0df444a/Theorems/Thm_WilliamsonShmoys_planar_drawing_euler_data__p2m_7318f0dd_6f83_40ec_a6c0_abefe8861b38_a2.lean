-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_7318f0dd_6f83_40ec_a6c0_abefe8861b38_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_data__p2m_7318f0dd_6f83_40ec_a6c0_abefe8861b38_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:41:58.733598+00:00
-- url     : https://prove2.me/theorems/02b5c4aa-87bb-4609-924c-f8cb942a1930
-- title:
--   Euler face data for a connected simple planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula and the face-boundary incidence bound. Derive a finite plane-map structure from the drawing, establish Euler’s formula, and count the two sides of each edge, including bridge traversals in face boundaries.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_data__p2m_7318f0dd_6f83_40ec_a6c0_abefe8861b38_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * G.edgeSet.ncard := by sorry
