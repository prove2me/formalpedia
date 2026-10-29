-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_maximal_extension__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
-- name    : WilliamsonShmoys.planar_drawingOn_edge_maximal_extension__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:05:33.108685+00:00
-- url     : https://prove2.me/theorems/67b4817e-7597-41bf-a105-99604f3fcd4d
-- title:
--   Finite drawable graphs have an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph that admits no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_edge_maximal_extension__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (hDraw : HasPlanarDrawingOn W) :
    ∃ X : SimpleGraph V, W ≤ X ∧ HasPlanarDrawingOn X ∧
      ∀ Y : SimpleGraph V, X ≤ Y → HasPlanarDrawingOn Y → Y = X := by sorry
