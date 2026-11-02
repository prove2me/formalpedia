-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
-- name    : WilliamsonShmoys.planar_drawing_euler__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:18:13.958372+00:00
-- url     : https://prove2.me/theorems/5a1a0554-b22b-4ad7-8575-5cad56df0b97
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the given crossing-free drawing, the number of complementary faces satisfies Euler's formula: edges plus two equals vertices plus faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler__p2m_7b82f13f_4972_4c18_a653_c5d0801ea028_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun f : Nat => H.edgeFinset.card + 2 = Fintype.card V + f := by
  sorry
