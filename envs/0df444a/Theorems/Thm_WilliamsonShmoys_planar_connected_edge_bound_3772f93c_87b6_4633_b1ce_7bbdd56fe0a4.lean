-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_bound_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- name    : WilliamsonShmoys.planar_connected_edge_bound_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T03:13:52.689038+00:00
-- url     : https://prove2.me/theorems/493b44de-b444-44e0-baf7-844554d5eb21
-- title:
--   Edge bound for connected planar drawings
-- statement:
--   Prove the planar edge bound for a connected graph with at least three vertices. This carries the main mathematics: derive Euler’s formula for the supplied drawing and bound the face-boundary incidences, including the argument that bridges do not create boundary walks of length below three under the simple-graph and vertex-count hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_edge_bound_3772f93c_87b6_4633_b1ce_7bbdd56fe0a4
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
