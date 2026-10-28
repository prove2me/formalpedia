-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_connected_repair_3e188728
-- name    : WilliamsonShmoys.planar_drawing_maximal_connected_repair_3e188728
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:11:46.758088+00:00
-- url     : https://prove2.me/theorems/0478d2c4-3ddc-4214-b3ac-6ca7564d2e8e
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A drawable graph on a finite nonempty ordered vertex type that is maximal among drawable supergraphs is connected. If it had distinct components, an arc in the complement of its drawing would allow an edge to be added without creating a crossing, contradicting maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_connected_repair_3e188728
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 0 < Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.Connected := by sorry
