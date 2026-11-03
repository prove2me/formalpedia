-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:15:13.806613+00:00
-- url     : https://prove2.me/theorems/73df37f1-f91e-4047-af57-f5368c90c677
-- title:
--   A drawable graph has an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under graph inclusion among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5adcef95_78da_42fb_a9d7_cfb89d379e66_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ H : SimpleGraph V, L ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L := by sorry
