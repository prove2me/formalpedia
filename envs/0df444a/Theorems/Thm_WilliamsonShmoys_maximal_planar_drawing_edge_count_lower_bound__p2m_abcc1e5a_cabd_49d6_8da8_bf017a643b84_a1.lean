-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:29:09.650769+00:00
-- url     : https://prove2.me/theorems/ff88384e-13a7-4e55-8777-790088f23a4a
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges. The geometric proof proceeds by showing maximality forces every face to be triangular and then applying Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_abcc1e5a_cabd_49d6_8da8_bf017a643b84_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L.edgeSet ⊆ M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
