-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:34.832722+00:00
-- url     : https://prove2.me/theorems/57f9e568-a017-4d51-b804-70963d2a6298
-- title:
--   Connected planar completion of a drawn graph
-- statement:
--   Any finite graph with a drawing as defined in the attached source is contained in a connected graph on the same vertices that also has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_completion__p2m_8555a31b_9435_47a6_94cc_80670b8cc7a7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
