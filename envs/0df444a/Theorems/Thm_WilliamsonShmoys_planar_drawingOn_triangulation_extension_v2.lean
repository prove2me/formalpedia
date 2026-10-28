-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_extension_v2
-- name    : WilliamsonShmoys.planar_drawingOn_triangulation_extension_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T07:05:15.029292+00:00
-- url     : https://prove2.me/theorems/15c376e4-071b-4130-9d92-218f4a22b09a
-- title:
--   Drawable supergraph with the maximal planar edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices is a subgraph of a drawable simple graph on the same vertices having exactly 3|V|−6 edges. For three vertices, the extension is the triangle. For larger graphs, extend the embedding to a maximal planar supergraph, triangulate its faces, and count using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_triangulation_extension_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hV : 3 <= Fintype.card V) :
    ∃ W : SimpleGraph V,
      (∀ {u v}, U.Adj u v → W.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
