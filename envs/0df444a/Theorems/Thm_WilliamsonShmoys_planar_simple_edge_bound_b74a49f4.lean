-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_b74a49f4
-- name    : WilliamsonShmoys.planar_simple_edge_bound_b74a49f4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:42:49.228478+00:00
-- url     : https://prove2.me/theorems/5c0a9770-4a93-427d-bc90-ac4826fcb74e
-- title:
--   Simple planar graph edge bound
-- statement:
--   A finite simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_edge_bound_b74a49f4 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
