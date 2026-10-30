-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_induced_edge_bound_retry3
-- name    : WilliamsonShmoys.planar_drawing_connected_induced_edge_bound_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:14:06.101468+00:00
-- url     : https://prove2.me/theorems/0b050164-1d49-4d39-aebe-37444558e83d
-- title:
--   Euler edge bound for connected induced subgraphs
-- statement:
--   Every connected induced subgraph on at least three vertices of a graph with a crossing-free drawing satisfies the planar Euler edge bound. Restrict the drawing to the subtype for `S`, then apply Euler’s formula and count face-edge incidences; the size hypothesis supplies the required boundary condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_induced_edge_bound_retry3 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (S : Finset V) (hS : 3 <= S.card) (hconn : (H.induce (↑S : Set V)).Connected) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : (H.induce (↑S : Set V)).edgeSet.ncard + 6 <= 3 * Fintype.card {v // v ∈ S} := by sorry
