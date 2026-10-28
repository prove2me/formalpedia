-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5
-- name    : WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T09:20:47.521717+00:00
-- url     : https://prove2.me/theorems/8938f63e-60b4-4adc-b119-4c4d94a26585
-- title:
--   Edge count of a maximal planar graph (repair)
-- statement:
--   An edge-maximal planar graph on a finite linearly ordered vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hmax : ∀ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M → L.edgeSet ⊆ M.edgeSet → M.edgeSet ⊆ L.edgeSet) : L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
