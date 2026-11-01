-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:35:47.50721+00:00
-- url     : https://prove2.me/theorems/0ac110bd-aaad-4255-8185-0d10e2119357
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   Under the target’s maximality hypothesis, the graph has at least 3|V|−6 edges. This supplies the lower-bound half independently of the general planar upper bound. A proof route is to show that maximality forces connectedness and triangular faces, then combine Euler’s formula with face-edge incidence counting. The bound of at least three vertices is retained for the triangulation and counting argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_21c82e8b_ea63_4b29_98bb_ab69d1fee3ec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
