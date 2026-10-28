-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_repair_025e7f85
-- name    : WilliamsonShmoys.planar_triangulation_extension_repair_025e7f85
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T22:10:50.520662+00:00
-- url     : https://prove2.me/theorems/0d3f2800-82dc-4ab9-ba1d-464ebc548881
-- title:
--   Extend a planar drawing to an exact edge-count completion
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_repair_025e7f85 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
