-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_strict_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- name    : WilliamsonShmoys.planar_drawing_disconnected_strict_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T20:52:39.527594+00:00
-- url     : https://prove2.me/theorems/8cea35d0-1902-4066-a769-e5349d5dbcd7
-- title:
--   Strict planar extension of a disconnected drawing
-- statement:
--   Every disconnected graph on a finite ordered vertex type with a drawing satisfying `HasPlanarDrawingOn` has a strict planar supergraph. The intended proof adds one edge joining two distinct components and constructs its arc in the complement of the finite drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_disconnected_strict_step__p2m_8e1589da_8236_4d2f_a43b_c94137df9ddf_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) (hDisconnected : ¬ H.Connected) :
    ∃ H' : SimpleGraph V, H < H' ∧ HasPlanarDrawingOn H' := by sorry
