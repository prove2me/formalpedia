-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_maximal__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
-- name    : WilliamsonShmoys.planar_supergraph_exists_maximal__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:12.299943+00:00
-- url     : https://prove2.me/theorems/dbde89e8-c849-4801-a07f-e697f1afc8ec
-- title:
--   Finite maximal planar supergraph exists
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.planar_supergraph_exists_maximal__p2m_9bfbc735_ec6d_4d27_8e0c_d58af3810de3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L →
        WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
