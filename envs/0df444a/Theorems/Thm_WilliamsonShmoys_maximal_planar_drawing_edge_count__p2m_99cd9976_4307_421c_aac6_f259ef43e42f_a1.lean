-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:12:09.961983+00:00
-- url     : https://prove2.me/theorems/53911c92-d38e-4043-bb6e-65b3932704cd
-- title:
--   Count the edges of an inclusion-maximal planar drawing
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3 * |V| - 6` edges. This isolates the topological work: show maximality forces a connected triangulation, then combine the triangular-face count with Euler’s formula. The vertex lower bound excludes the small cases where the formula does not apply.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M) :
    M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
