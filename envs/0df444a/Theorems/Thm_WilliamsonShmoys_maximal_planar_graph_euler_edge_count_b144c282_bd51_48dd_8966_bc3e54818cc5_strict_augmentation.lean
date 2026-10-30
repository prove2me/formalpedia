-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_strict_augmentation
-- name    : WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_strict_augmentation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:34:21.641209+00:00
-- url     : https://prove2.me/theorems/734e4794-db68-4b09-bc19-ba0f69b15c16
-- title:
--   Sparse planar graphs admit a strict planar edge augmentation
-- statement:
--   A finite simple planar graph on at least three vertices whose edge count is below the maximal planar count has a planar strict supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_euler_edge_count_b144c282_bd51_48dd_8966_bc3e54818cc5_strict_augmentation {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hsparse : L.edgeSet.ncard + 6 < 3 * Fintype.card V) : ∃ M : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn M ∧ L.edgeSet ⊆ M.edgeSet ∧ ¬ M.edgeSet ⊆ L.edgeSet := by sorry
