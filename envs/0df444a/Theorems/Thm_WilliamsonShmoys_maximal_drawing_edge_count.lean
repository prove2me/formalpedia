-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_edge_count
-- name    : WilliamsonShmoys.maximal_drawing_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:06:55.551112+00:00
-- url     : https://prove2.me/theorems/e48caf0e-3ad2-45b7-8ecc-4477eb30fb9d
-- title:
--   An edge-maximal planar graph has 3n−6 edges
-- statement:
--   A planar graph with at least three vertices that has no proper planar supergraph on the same vertices has exactly 3n−6 edges. Maximality forces triangular faces; Euler’s formula and counting face-edge incidences yield the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ G : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → G.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn G → G = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
