-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
-- name    : WilliamsonShmoys.maximal_planar_euler_count__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:23:02.417811+00:00
-- url     : https://prove2.me/theorems/ca3bbeaf-b99d-433d-8549-4f9fe71c79f9
-- title:
--   An inclusion-maximal drawable graph has the Euler edge count
-- statement:
--   If a drawable simple graph on at least three vertices has no strictly larger drawable supergraph on the same vertices, then its edge count is 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.maximal_planar_euler_count__p2m_1dc633c7_70a8_4274_883e_7335c1c0b3c4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : forall K : SimpleGraph V,
      N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = N)
    (hV : 3 <= Fintype.card V) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
