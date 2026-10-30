-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_upper_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99
-- name    : WilliamsonShmoys.maximal_planar_edge_count_upper_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:45:19.272314+00:00
-- url     : https://prove2.me/theorems/9a40956c-04dd-448b-9ab6-80f8d2edf7ce
-- title:
--   Euler upper bound for a finite planar graph
-- statement:
--   A simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_upper_bound_c06a69a3_ca91_45ac_86f5_c61df4ae7c99 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hCard : 3 <= Fintype.card V) : L.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
