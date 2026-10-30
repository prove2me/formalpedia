-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_triangulation
-- name    : WilliamsonShmoys.planar_extension_to_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:57:45.007805+00:00
-- url     : https://prove2.me/theorems/4526b245-3df2-4939-9e5f-e0cd6084d3f2
-- title:
--   Extend a planar drawing to an edge-dense planar supergraph
-- statement:
--   Every finite graph with a crossing-free drawing on at least three vertices is a subgraph of a graph on the same vertices that also has a crossing-free drawing and at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    exists M : SimpleGraph V,
      L <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
      3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
