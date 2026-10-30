-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_f1f92bb7
-- name    : WilliamsonShmoys.maximal_planar_edge_count_f1f92bb7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:26:49.201204+00:00
-- url     : https://prove2.me/theorems/1cf7237a-1509-4e24-a7f5-c50e7a3d8def
-- title:
--   The edge count of a maximal planar graph
-- statement:
--   A finite edge-maximal simple planar graph on at least three vertices has exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_f1f92bb7 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
