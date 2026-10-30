-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:18:27.784448+00:00
-- url     : https://prove2.me/theorems/32374ca1-a20e-4fd1-98de-f95812b47536
-- title:
--   An inclusion-maximal planar drawing has the exact edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph has exactly 3|V|−6 edges. The proof route is to show maximality forces every face to be triangular and then count face-edge incidences using Euler’s formula, treating the three-vertex boundary case explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hMaximal : ∀ K : SimpleGraph V,
      N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
