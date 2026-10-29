-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_extension__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7
-- name    : WilliamsonShmoys.planar_edge_maximal_extension__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T04:03:26.497068+00:00
-- url     : https://prove2.me/theorems/9eb228d8-54c6-47fb-b53c-bfe206bbe26f
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs containing it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_maximal_extension__p2m_e69220cf_5cc1_4342_a84f_9ccd3d593737_a7
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\ WilliamsonShmoys.HasPlanarDrawingOn L /\
        (forall M : SimpleGraph V,
          L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by sorry
