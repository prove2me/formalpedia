-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_supergraph_fixed_vertices
-- name    : WilliamsonShmoys.planar_drawing_maximal_supergraph_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T16:05:51.93966+00:00
-- url     : https://prove2.me/theorems/5454159c-6517-4cce-a170-5de785b4e447
-- title:
--   Maximal drawable supergraph on fixed vertices
-- statement:
--   Every drawable graph on a finite vertex set has a drawable supergraph on that same set that is maximal under edge-set inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_supergraph_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R) :
    ∃ H : SimpleGraph V,
      R.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet → H.edgeSet ≠ K.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
