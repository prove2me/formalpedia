-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_extremal_supergraph_a67a2052
-- name    : WilliamsonShmoys.planar_drawing_has_extremal_supergraph_a67a2052
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T05:11:19.510244+00:00
-- url     : https://prove2.me/theorems/12dbf1fc-26d9-402d-a210-d21418dde990
-- title:
--   Planar drawing extends to an extremal supergraph
-- statement:
--   Every graph with a crossing-free drawing on at least three finite ordered vertices is a subgraph of a graph on the same vertices with a crossing-free drawing and exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_extremal_supergraph_a67a2052
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hCard : 3 <= Fintype.card V) :
    exists Y : SimpleGraph V,
      HasPlanarDrawingOn Y /\
      (forall u v, X.Adj u v -> Y.Adj u v) /\
      Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
