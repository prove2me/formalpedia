-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_one_edge_extension
-- name    : WilliamsonShmoys.planar_drawing_one_edge_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-28T05:18:08.827332+00:00
-- url     : https://prove2.me/theorems/d5a0b35e-99d7-421f-9928-bac2c76fc264
-- title:
--   Add a planar bridge between disconnected vertices
-- statement:
--   For any finite drawn graph that is disconnected, add a planar edge joining two vertices that were in different connected components, while retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_one_edge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ K.Reachable u v ∧ H.Adj u v := by sorry
