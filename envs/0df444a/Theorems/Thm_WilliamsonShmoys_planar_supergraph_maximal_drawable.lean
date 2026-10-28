-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_drawable
-- name    : WilliamsonShmoys.planar_supergraph_maximal_drawable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:11:30.039294+00:00
-- url     : https://prove2.me/theorems/9f54537b-a473-422d-8d2a-f8efa4ee0a83
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite vertex type is contained in a drawable graph that has no proper drawable supergraph on that same type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_drawable
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V,
      H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V,
        J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = J := by sorry
