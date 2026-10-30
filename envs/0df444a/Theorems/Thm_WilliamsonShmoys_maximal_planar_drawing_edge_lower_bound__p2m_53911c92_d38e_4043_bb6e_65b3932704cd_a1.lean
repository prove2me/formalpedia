-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:31:46.917981+00:00
-- url     : https://prove2.me/theorems/abc6942a-8a99-4355-badf-59d2c1ffe2f0
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   An inclusion-maximal graph among those admitting a crossing-free drawing, on at least three vertices, has at least $3|V|-6$ edges. Extend its drawing to a triangulation using the same vertex set; maximality forces the extension to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_53911c92_d38e_4043_bb6e_65b3932704cd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    3 * Fintype.card V <= M.edgeSet.ncard + 6 := by sorry
