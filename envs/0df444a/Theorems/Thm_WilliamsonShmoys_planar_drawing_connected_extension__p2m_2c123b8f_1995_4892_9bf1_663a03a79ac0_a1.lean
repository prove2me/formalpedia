-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:51.570972+00:00
-- url     : https://prove2.me/theorems/fb475999-bbbb-4d3f-8e03-a58caa743876
-- title:
--   Connect a finite planar drawing by adding edges
-- statement:
--   Every drawable finite simple graph on at least three vertices has a connected drawable simple supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_2c123b8f_1995_4892_9bf1_663a03a79ac0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ T.Connected ∧ HasPlanarDrawingOn T := by sorry
