-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subgraph__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
-- name    : WilliamsonShmoys.planar_drawing_subgraph__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:06:34.379367+00:00
-- url     : https://prove2.me/theorems/f0ce7208-ecfc-49a9-9c5e-900a078a5b56
-- title:
--   Planarity is inherited by subgraphs
-- statement:
--   If G is a subgraph of H and H has a crossing-free drawing, then G has a crossing-free drawing. Restricting the existing drawing to G's edges proves the claim, including the nonintersection conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_subgraph__p2m_11371f3f_0d50_4c49_9eed_89dfd5ac185f_a1 {V : Type} [Fintype V] [LinearOrder V] {G H : SimpleGraph V} (hGH : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
