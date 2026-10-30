-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_relation__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_relation__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:45:43.845984+00:00
-- url     : https://prove2.me/theorems/bcebeefe-2913-4eb1-b635-235f1aab9c7b
-- title:
--   Euler face-count identity for a planar drawing
-- statement:
--   For a finite connected graph with the specified crossing-free drawing, there is a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_relation__p2m_dbab630e_c01d_4b47_9ab6_dd56c8211fc8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    Exists (fun f : Nat => Fintype.card V + f = K.edgeSet.ncard + 2) := by sorry
