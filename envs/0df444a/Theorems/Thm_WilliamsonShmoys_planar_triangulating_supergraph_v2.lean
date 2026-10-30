-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulating_supergraph_v2
-- name    : WilliamsonShmoys.planar_triangulating_supergraph_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:56:56.036672+00:00
-- url     : https://prove2.me/theorems/b456ae06-0209-41ef-b2a4-b7b939f821fd
-- title:
--   Planar triangulating supergraph on the same vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex type with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulating_supergraph_v2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) : ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
