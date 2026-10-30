-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T09:18:18.224672+00:00
-- url     : https://prove2.me/theorems/e6303700-9a11-44a1-af5b-40c87d66fc20
-- title:
--   Finite planar completion to an inclusion-maximal drawing
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type that has no strictly larger drawable supergraph. This is the finite topological augmentation step; it does not assert an edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_52c72b1a_727a_4125_917a_c27d4ca055ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
