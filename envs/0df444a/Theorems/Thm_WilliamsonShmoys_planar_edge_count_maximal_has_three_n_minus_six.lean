-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_has_three_n_minus_six
-- name    : WilliamsonShmoys.planar_edge_count_maximal_has_three_n_minus_six
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:55:15.939077+00:00
-- url     : https://prove2.me/theorems/40b870a7-75c4-4cdd-8646-4ea9bba5e8ec
-- title:
--   An edge-maximal planar graph has three n minus six edges
-- statement:
--   A simple graph on at least three vertices that has a planar drawing and is maximal among planar supergraphs on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_maximal_has_three_n_minus_six
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H <= K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
