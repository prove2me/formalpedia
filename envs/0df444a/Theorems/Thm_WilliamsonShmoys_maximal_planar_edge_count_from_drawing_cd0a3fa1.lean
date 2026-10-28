-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_from_drawing_cd0a3fa1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_from_drawing_cd0a3fa1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T00:19:00.825882+00:00
-- url     : https://prove2.me/theorems/2b33bd61-3727-420c-83bd-70245ae39680
-- title:
--   An edge-maximal planar graph has 3n minus 6 edges
-- statement:
--   A planar simple graph on at least three vertices that admits no proper planar supergraph on the same vertex set has exactly 3n − 6 edges. The boundary n = 3 is included. The independent proof route is to obtain a plane embedding from the supplied arc drawing, derive triangular face boundaries from maximality, then count face-edge incidences and apply Euler’s formula. This is the remaining core topological obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_from_drawing_cd0a3fa1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      (∀ ⦃u v : V⦄, K.Adj u v → G.Adj u v)) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
