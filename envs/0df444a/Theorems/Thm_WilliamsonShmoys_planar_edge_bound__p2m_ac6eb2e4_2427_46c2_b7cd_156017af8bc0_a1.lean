-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- name    : WilliamsonShmoys.planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:33:46.401924+00:00
-- url     : https://prove2.me/theorems/dccace07-71ac-4a60-a538-34fe866b4edd
-- title:
--   Euler edge bound for a drawable planar graph
-- statement:
--   A simple graph with a crossing-free drawing on at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound__p2m_ac6eb2e4_2427_46c2_b7cd_156017af8bc0_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
