-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_set_of_planar_drawings__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
-- name    : WilliamsonShmoys.finite_set_of_planar_drawings__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:00.726352+00:00
-- url     : https://prove2.me/theorems/739916a8-5e53-44d4-a730-f6ff38f47061
-- title:
--   Finiteness of drawable simple graphs on a finite vertex type
-- statement:
--   The simple graphs on a finite vertex type form a finite set, so the subset consisting of graphs with a planar drawing is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_set_of_planar_drawings__p2m_a402c68a_d7fd_45a8_9fd3_2080e97d0c7e_a2 {V : Type} [Fintype V] [LinearOrder V] : ({N : SimpleGraph V | WilliamsonShmoys.HasPlanarDrawingOn N} : Set (SimpleGraph V)).Finite := by sorry
