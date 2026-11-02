-- Prove2me | Theorems.Thm_planar_drawing_on_subgraph__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
-- name    : planar_drawing_on_subgraph__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:23:58.249462+00:00
-- url     : https://prove2.me/theorems/8502f3b2-2f52-4edd-ae77-bfadde9584dc
-- title:
--   Planar drawing is inherited by subgraphs
-- statement:
--   A graph obtained by deleting edges from a graph with a crossing-free drawing has a crossing-free drawing on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem planar_drawing_on_subgraph__p2m_3f244f53_8936_4715_8547_0063dd70ff12_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by
  sorry
