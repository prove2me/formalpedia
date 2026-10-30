-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connect_components__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- name    : WilliamsonShmoys.planar_drawing_connect_components__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-29T08:45:29.775796+00:00
-- url     : https://prove2.me/theorems/ae236b28-36d0-427c-b659-9ad0e6481b28
-- title:
--   Connect components of a planar drawing
-- statement:
--   Any finite graph with a crossing-free drawing can be extended on the same vertices to a connected graph that still has a crossing-free drawing and contains all its edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connect_components__p2m_b17d3809_e307_4597_82b6_1d4f1ebd7e38_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      P.edgeSet.ncard ≤ Q.edgeSet.ncard := by sorry
