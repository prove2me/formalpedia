-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound
-- name    : WilliamsonShmoys.planar_connected_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:51:01.710431+00:00
-- url     : https://prove2.me/theorems/aad8d6c4-95b3-4d1e-a390-040b065cc1b6
-- title:
--   Connected simple planar graphs satisfy the edge bound
-- statement:
--   A connected simple graph on at least three vertices with a crossing-free drawing has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_bound {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
