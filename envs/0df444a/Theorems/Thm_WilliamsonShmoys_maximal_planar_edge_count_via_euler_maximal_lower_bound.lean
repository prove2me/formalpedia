-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler_maximal_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_via_euler_maximal_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T20:52:48.018285+00:00
-- url     : https://prove2.me/theorems/f3ca7aec-4482-4122-8f8e-1d6a4f78bad3
-- title:
--   Maximality forces the triangulation lower bound
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3|V|−6 edges. A proof route is to use maximality to establish connectedness and rule out faces that can be subdivided by adding a noncrossing edge; triangulation and Euler’s formula then give the lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_via_euler_maximal_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hSmax : ∀ T : SimpleGraph V,
      S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    3 * Fintype.card V - 6 ≤ S.edgeSet.ncard := by sorry
