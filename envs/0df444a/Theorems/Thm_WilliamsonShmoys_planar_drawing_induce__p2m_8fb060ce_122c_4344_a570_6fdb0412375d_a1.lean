-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a1
-- name    : WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:35:26.387054+00:00
-- url     : https://prove2.me/theorems/edf48b59-c0fc-4567-95fc-46114229b61a
-- title:
--   Planar drawing restricts to induced subgraphs
-- statement:
--   If a finite linearly ordered simple graph has the specified crossing-free drawing, then the induced graph on any vertex subset has the same kind of drawing, using restricted vertex points and the original curves.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_induce__p2m_8fb060ce_122c_4344_a570_6fdb0412375d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (s : Set V) :
    letI : Fintype {v // v ∈ s} := Fintype.ofFinite _
    HasPlanarDrawingOn (N.induce s) := by sorry
