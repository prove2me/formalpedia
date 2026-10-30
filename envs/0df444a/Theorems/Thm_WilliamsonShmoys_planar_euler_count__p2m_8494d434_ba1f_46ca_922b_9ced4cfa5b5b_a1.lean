-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_count__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
-- name    : WilliamsonShmoys.planar_euler_count__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:57.691983+00:00
-- url     : https://prove2.me/theorems/535aede5-1ca2-40bc-b03c-6fd9200f157c
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied planar drawing, there is a face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_euler_count__p2m_8494d434_ba1f_46ca_922b_9ced4cfa5b5b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
