-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_euler_count
-- name    : WilliamsonShmoys.planar_edge_maximal_euler_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:42:45.920097+00:00
-- url     : https://prove2.me/theorems/e009610b-35ce-4c4c-b731-e4f40d2f30b6
-- title:
--   An inclusion maximal planar graph has the Euler edge count
-- statement:
--   For at least three vertices, an inclusion maximal simple graph with a planar drawing has exactly three times the vertex count minus six edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_euler_count {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M.edgeSet ⊆ N.edgeSet → N.edgeSet ⊆ M.edgeSet) (hV : 3 ≤ Fintype.card V) : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
