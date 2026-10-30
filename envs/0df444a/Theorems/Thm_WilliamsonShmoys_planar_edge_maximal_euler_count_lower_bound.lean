-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_euler_count_lower_bound
-- name    : WilliamsonShmoys.planar_edge_maximal_euler_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:05:06.041992+00:00
-- url     : https://prove2.me/theorems/027219c2-46b7-445c-8cc6-7c65fe9ad995
-- title:
--   Lower bound from maximality of a planar drawing
-- statement:
--   An inclusion-maximal graph under `HasPlanarDrawingOn`, with at least three vertices, has at least `3 |V| - 6` edges, expressed without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_euler_count_lower_bound {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hmax : ∀ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N → M.edgeSet ⊆ N.edgeSet → N.edgeSet ⊆ M.edgeSet) (hV : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
