-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:53:45.70298+00:00
-- url     : https://prove2.me/theorems/5db6a80d-54aa-4e0a-9bf3-96c293216517
-- title:
--   Edge bound for a finite graph with a crossing-free drawing
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_58a549ee_4768_4664_9403_907071b96f48_a4 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hcard : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
