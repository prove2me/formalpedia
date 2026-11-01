-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:43.6155+00:00
-- url     : https://prove2.me/theorems/bf0a7b72-11ad-4656-97eb-ed64d269b026
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite vertex type with at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_a05c061d_946f_411a_b5cf_34f022290b66_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      ∀ u v, L.Adj u v → K.Adj u v) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
