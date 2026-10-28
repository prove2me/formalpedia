-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_exists_maximal_supergraph_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- name    : WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:33:45.02587+00:00
-- url     : https://prove2.me/theorems/34c80f67-d1b3-4653-93fa-c0b89134e902
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same type. The finite set of simple graphs permits choosing a drawable supergraph with the greatest edge count; any drawable strict supergraph would have more edges. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_exists_maximal_supergraph_a6cc6ce2_4479_4e22_ad6e_c928f195198d
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ M : SimpleGraph V,
      K ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
