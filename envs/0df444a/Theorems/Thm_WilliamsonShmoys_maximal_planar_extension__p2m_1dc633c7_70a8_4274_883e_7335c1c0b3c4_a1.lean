-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:22:54.15001+00:00
-- url     : https://prove2.me/theorems/73c85c29-4333-4692-baee-7210fe30cead
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   Every drawable graph on the finite vertex type has a drawable supergraph that is inclusion maximal among drawable graphs on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_extension__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      forall K : SimpleGraph V,
        N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N := by sorry
