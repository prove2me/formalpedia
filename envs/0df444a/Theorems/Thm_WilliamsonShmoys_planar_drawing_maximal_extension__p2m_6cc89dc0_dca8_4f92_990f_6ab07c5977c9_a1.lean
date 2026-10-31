-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:15.520322+00:00
-- url     : https://prove2.me/theorems/8c20c3de-e0e6-4d41-88fb-de4af60b0786
-- title:
--   Finite maximal planar extension
-- statement:
--   Every graph with a planar drawing on a finite vertex set is contained in a graph with a planar drawing that is maximal under edge inclusion on that same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_6cc89dc0_dca8_4f92_990f_6ab07c5977c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    Exists fun T : SimpleGraph V =>
      And (LE.le H T) (And (HasPlanarDrawingOn T)
      (forall T' : SimpleGraph V, LE.le T T' -> HasPlanarDrawingOn T' -> T' = T)) := by sorry
