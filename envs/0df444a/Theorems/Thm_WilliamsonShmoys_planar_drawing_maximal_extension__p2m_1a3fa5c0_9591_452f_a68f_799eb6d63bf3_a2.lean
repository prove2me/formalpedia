-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_1a3fa5c0_9591_452f_a68f_799eb6d63bf3_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1a3fa5c0_9591_452f_a68f_799eb6d63bf3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T13:09:30.29599+00:00
-- url     : https://prove2.me/theorems/f933d8ea-7a96-4f7a-b789-659eeb31cdb8
-- title:
--   Maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_1a3fa5c0_9591_452f_a68f_799eb6d63bf3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    Exists fun K : SimpleGraph V =>
      And (Set.Subset H.edgeSet K.edgeSet)
        (And (WilliamsonShmoys.HasPlanarDrawingOn K)
          (forall M : SimpleGraph V,
            Set.Subset K.edgeSet M.edgeSet ->
            WilliamsonShmoys.HasPlanarDrawingOn M ->
            Set.Subset M.edgeSet K.edgeSet)) := by
  sorry
