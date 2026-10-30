-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation
-- name    : WilliamsonShmoys.planar_supergraph_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:14:15.740126+00:00
-- url     : https://prove2.me/theorems/d963bbfb-1ab1-4954-bb2b-6563459daa76
-- title:
--   Planar completion to a triangulation
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three is contained in a graph with a crossing-free drawing on the same vertices and exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_triangulation {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
