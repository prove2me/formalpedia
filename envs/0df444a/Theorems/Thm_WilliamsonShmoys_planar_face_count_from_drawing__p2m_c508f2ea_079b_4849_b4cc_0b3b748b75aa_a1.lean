-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_from_drawing__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
-- name    : WilliamsonShmoys.planar_face_count_from_drawing__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:02.875012+00:00
-- url     : https://prove2.me/theorems/7b82f13f-4972-4c18-a653-c5d0801ea028
-- title:
--   Euler face count and facial degree bound from a planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with the given crossing-free drawing, there is a finite face count satisfying Euler’s formula and the bound that total facial degree is at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_face_count_from_drawing__p2m_c508f2ea_079b_4849_b4cc_0b3b748b75aa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hn : Nat.le 3 (Fintype.card V)) :
    ∃ f : Nat,
      H.edgeFinset.card + 2 = Fintype.card V + f ∧
      3 * f ≤ 2 * H.edgeFinset.card := by
  sorry
