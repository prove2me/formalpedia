-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_same_vertex_count_20261027
-- name    : WilliamsonShmoys.maximal_planar_extension_same_vertex_count_20261027
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T20:13:26.227831+00:00
-- url     : https://prove2.me/theorems/12e592dc-313e-4019-b7fa-ab27702be44e
-- title:
--   Planar extension with maximal planar edge count
-- statement:
--   Every finite planar graph on at least three vertices is contained in a planar graph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension_same_vertex_count_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
