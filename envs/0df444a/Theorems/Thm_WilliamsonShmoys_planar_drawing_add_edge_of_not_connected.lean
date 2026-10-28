-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_of_not_connected
-- name    : WilliamsonShmoys.planar_drawing_add_edge_of_not_connected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:49:02.299356+00:00
-- url     : https://prove2.me/theorems/2cf22aed-fdac-4e1e-858d-81916aaceae8
-- title:
--   A disconnected planar drawing has a strict drawable supergraph
-- statement:
--   Every disconnected graph on a finite nonempty ordered vertex type with a drawing satisfying HasPlanarDrawingOn has a strict drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_of_not_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ HasPlanarDrawingOn K := by sorry
