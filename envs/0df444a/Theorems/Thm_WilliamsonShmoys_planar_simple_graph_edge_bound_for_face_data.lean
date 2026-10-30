-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_for_face_data
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:41:11.756168+00:00
-- url     : https://prove2.me/theorems/2688d621-2d1a-429d-9022-7ec83727c981
-- title:
--   Simple planar graph edge bound for face data
-- statement:
--   A connected simple planar graph with at least three vertices has at most `3V - 6` edges, written without truncated subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_for_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    J.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
