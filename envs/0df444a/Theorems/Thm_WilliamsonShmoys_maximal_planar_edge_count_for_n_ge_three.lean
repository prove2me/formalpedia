-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_n_ge_three
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_n_ge_three
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:20:34.283781+00:00
-- url     : https://prove2.me/theorems/c06a69a3-ca91-45ac-86f5-c61df4ae7c99
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   Every edge-maximal graph with a crossing-free drawing on at least three vertices has exactly 3|V|-6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_for_n_ge_three {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) (hCard : 3 ≤ Fintype.card V) : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
