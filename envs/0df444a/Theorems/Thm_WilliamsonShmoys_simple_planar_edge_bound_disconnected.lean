-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_disconnected
-- name    : WilliamsonShmoys.simple_planar_edge_bound_disconnected
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:58:20.362363+00:00
-- url     : https://prove2.me/theorems/68c1edf9-17a2-4a72-8230-5c585ed08559
-- title:
--   Simple planar edge bound for disconnected graphs
-- statement:
--   A disconnected finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.simple_planar_edge_bound_disconnected
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLdraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ L.Connected) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
