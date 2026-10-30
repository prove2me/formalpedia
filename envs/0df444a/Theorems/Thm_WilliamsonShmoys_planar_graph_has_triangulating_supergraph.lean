-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:23:39.948855+00:00
-- url     : https://prove2.me/theorems/2bc941c7-4537-4b44-b809-b914ee8ab288
-- title:
--   Every finite planar drawing has a triangulating supergraph
-- statement:
--   Any finite simple graph on at least three ordered vertices with a crossing-free drawing has a planar supergraph on the same vertices with exactly 3|V|−6 edges. This is the standard extension-to-a-triangulation fact together with Euler’s formula; proving it requires handling the drawing’s faces and adding noncrossing diagonals.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulating_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
