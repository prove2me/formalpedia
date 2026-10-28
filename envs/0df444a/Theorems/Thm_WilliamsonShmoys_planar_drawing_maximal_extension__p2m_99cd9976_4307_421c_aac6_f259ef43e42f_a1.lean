-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:12:02.356269+00:00
-- url     : https://prove2.me/theorems/26c84632-20c9-4c4b-b46d-f4a8186aef91
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under inclusion. The proof route is finite maximization of edge count over all eligible simple graphs; it needs no vertex-count lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_99cd9976_4307_421c_aac6_f259ef43e42f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    exists M : SimpleGraph V,
      N <= M /\ WilliamsonShmoys.HasPlanarDrawingOn M /\
        forall K : SimpleGraph V, M <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = M := by sorry
