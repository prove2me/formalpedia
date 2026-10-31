-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_between_components__p2m_da8118fe_17fb_4c93_a2d6_08f851f61791_a1
-- name    : WilliamsonShmoys.planar_extension_between_components__p2m_da8118fe_17fb_4c93_a2d6_08f851f61791_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:46:47.312987+00:00
-- url     : https://prove2.me/theorems/93b196f9-a089-4227-b31a-98dfbb27d1c3
-- title:
--   Bridge two components of a planar drawing
-- statement:
--   Given a crossing-free drawing and two vertices in different connected components, add an edge between them while preserving a crossing-free drawing on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_extension_between_components__p2m_da8118fe_17fb_4c93_a2d6_08f851f61791_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (u v : V)
    (hreach : ¬ L.Reachable u v) :
    ∃ H : SimpleGraph V, L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Adj u v ∧ ¬ L.Adj u v := by sorry
