-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_exists__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:00:22.578531+00:00
-- url     : https://prove2.me/theorems/16e1af44-0130-4871-bc35-059dc1c2bab8
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that has no drawable strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_exists__p2m_a419e21a_2978_404e_8b1f_5dd1d0da8bd8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by
  sorry
