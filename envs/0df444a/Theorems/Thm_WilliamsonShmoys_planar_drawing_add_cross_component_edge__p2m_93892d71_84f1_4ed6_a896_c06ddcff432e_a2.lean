-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_cross_component_edge__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
-- name    : WilliamsonShmoys.planar_drawing_add_cross_component_edge__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T07:33:35.555848+00:00
-- url     : https://prove2.me/theorems/5e89dc1f-2791-450c-9ff2-47751cdc5a12
-- title:
--   Add a drawable edge between distinct components
-- statement:
--   Extend a disconnected graph with a crossing-free drawing by an edge joining vertices in distinct original components, retaining all original edges and a crossing-free drawing. A proof route is to connect the embedded components through their common unbounded face, avoiding the finite existing drawing. This is the topological core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_cross_component_edge__p2m_93892d71_84f1_4ed6_a896_c06ddcff432e_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hconn : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry
