-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- name    : WilliamsonShmoys.planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T18:31:06.795967+00:00
-- url     : https://prove2.me/theorems/76da28cf-203d-4767-b5f5-69763f85c611
-- title:
--   Connect a disconnected finite plane drawing by augmentation
-- statement:
--   Any disconnected finite graph with the supplied crossing-free drawing and at least three vertices has a connected planar supergraph on the same vertices. This isolates the geometric augmentation; it does not assert an edge-count bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_supergraph_of_disconnected_drawing__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2 {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hdis : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H := by sorry
