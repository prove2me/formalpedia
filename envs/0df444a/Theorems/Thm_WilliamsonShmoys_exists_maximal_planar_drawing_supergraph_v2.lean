-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_v2
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:10:02.076206+00:00
-- url     : https://prove2.me/theorems/8425ea74-0e1f-468f-b323-12d60415b1ee
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertex set that is maximal under edge inclusion. Choose a drawable supergraph with the largest edge count; any drawable graph containing it must then have the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hNdraw : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      ∀ Q : SimpleGraph V,
        P ≤ Q → WilliamsonShmoys.HasPlanarDrawingOn Q → Q ≤ P := by sorry
