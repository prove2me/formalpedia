-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_triangulated_supergraph
-- name    : WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:27:55.559817+00:00
-- url     : https://prove2.me/theorems/c1858b2a-2070-4db6-a0f4-ae5f3dacb3cc
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   Every drawable finite simple graph on at least three vertices is a subgraph of a drawable triangulation on the same vertex set, with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ S : SimpleGraph V, R ≤ S ∧
      WilliamsonShmoys.HasPlanarDrawingOn S ∧
      S.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
