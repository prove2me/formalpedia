-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:43.400661+00:00
-- url     : https://prove2.me/theorems/21c82e8b-ea63-4b29-98bb-ab69d1fee3ec
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A simple graph on at least three vertices that is maximal among graphs admitting the supplied planar drawing has exactly 3|V|−6 edges. A proof route is to show maximality forces a connected triangulation, then use Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_acd844a2_f18b_4cf8_8cd2_2591d79fbd14_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
