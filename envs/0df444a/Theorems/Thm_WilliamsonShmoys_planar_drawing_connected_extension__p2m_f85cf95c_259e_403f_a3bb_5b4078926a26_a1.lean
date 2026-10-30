-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:44:36.171039+00:00
-- url     : https://prove2.me/theorems/c5002bd9-287e-4c4a-8f25-d9d45db0800d
-- title:
--   Connected planar extension of a finite drawing
-- statement:
--   Any finite drawable simple graph with at least three vertices can be extended, by adding edges on the same vertex set, to a connected drawable simple graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_f85cf95c_259e_403f_a3bb_5b4078926a26_a1
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hT : HasPlanarDrawingOn T) :
    ∃ H : SimpleGraph V, T.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
