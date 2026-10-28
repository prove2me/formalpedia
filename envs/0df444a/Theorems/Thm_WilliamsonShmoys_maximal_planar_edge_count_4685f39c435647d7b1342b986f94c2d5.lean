-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_4685f39c435647d7b1342b986f94c2d5
-- name    : WilliamsonShmoys.maximal_planar_edge_count_4685f39c435647d7b1342b986f94c2d5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:56:57.137124+00:00
-- url     : https://prove2.me/theorems/4b22e7d2-b71e-4020-894e-49f8934bba7d
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A planar graph on at least three vertices that is maximal under edge inclusion among planar graphs on the same vertex type has exactly `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_4685f39c435647d7b1342b986f94c2d5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H →
      G.edgeSet ⊆ H.edgeSet →
      H.edgeSet ⊆ G.edgeSet) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
