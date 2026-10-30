-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_c00979a8
-- name    : WilliamsonShmoys.maximal_planar_edge_bound_c00979a8
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:46:01.121362+00:00
-- url     : https://prove2.me/theorems/79ae7de0-043b-4037-8bc4-ee07637ddb0a
-- title:
--   Edge bound for a maximal planar graph
-- statement:
--   A connected inclusion-maximal graph with the specified planar drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound_c00979a8 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hconn : L.Connected) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
