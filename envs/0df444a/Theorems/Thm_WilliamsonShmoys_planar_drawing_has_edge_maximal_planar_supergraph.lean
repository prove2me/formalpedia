-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_planar_supergraph
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:09:48.282869+00:00
-- url     : https://prove2.me/theorems/6b41285b-84d5-4ed1-b491-484dfab224aa
-- title:
--   Planar drawing extends to an edge-maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices that is maximal among planar supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
