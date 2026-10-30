-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:45:16.442415+00:00
-- url     : https://prove2.me/theorems/a8cc1130-463b-4047-8c5c-3f482bfddd2a
-- title:
--   A maximal planar drawing is connected
-- statement:
--   An inclusion-maximal graph admitting a crossing-free drawing on a finite ordered vertex type of size at least three is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_connected__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    H.Connected := by sorry
