-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:13:21.239348+00:00
-- url     : https://prove2.me/theorems/c905941a-4320-416d-8dee-938a51cbef85
-- title:
--   Add a planar bridge between distinct components
-- statement:
--   Every disconnected finite planar graph can be extended to a planar graph by adding an edge between vertices that were in different connected components. The geometric proof redraws the components separately and routes the new edge through their exterior.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_bridge_between_components__p2m_6542605d_05b7_4349_89df_2d6e0eb6b2d4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn K)
    (hdisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
      HasPlanarDrawingOn L := by sorry
