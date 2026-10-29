-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_upper_bound_of_maximal_planar_drawing__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
-- name    : WilliamsonShmoys.edge_count_upper_bound_of_maximal_planar_drawing__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:59:09.227188+00:00
-- url     : https://prove2.me/theorems/38a90fc3-dea3-4c9f-8a52-b5002f138593
-- title:
--   Euler edge bound for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertex type satisfies the planar Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_upper_bound_of_maximal_planar_drawing__p2m_0ef6cdd6_0074_4ddf_9918_5e48acac88b4_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
