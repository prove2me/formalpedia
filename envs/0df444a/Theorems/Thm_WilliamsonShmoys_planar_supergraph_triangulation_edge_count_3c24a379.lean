-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation_edge_count_3c24a379
-- name    : WilliamsonShmoys.planar_supergraph_triangulation_edge_count_3c24a379
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:50:32.7832+00:00
-- url     : https://prove2.me/theorems/f1f92bb7-7559-4d21-aa69-7902873d906a
-- title:
--   Triangulated planar supergraph with the maximal edge count
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices is contained on the same vertex set in a crossing-free graph with exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_triangulation_edge_count_3c24a379 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
