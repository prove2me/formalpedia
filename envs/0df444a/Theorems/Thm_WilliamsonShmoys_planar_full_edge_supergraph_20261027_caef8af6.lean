-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_full_edge_supergraph_20261027_caef8af6
-- name    : WilliamsonShmoys.planar_full_edge_supergraph_20261027_caef8af6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:36:17.758395+00:00
-- url     : https://prove2.me/theorems/d800f429-0dcb-44c3-989f-b60bdda1f2ea
-- title:
--   Planar supergraph attaining the edge bound
-- statement:
--   Every simply drawn planar graph on at least three vertices has a planar supergraph on the same vertices with exactly 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_full_edge_supergraph_20261027_caef8af6
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
