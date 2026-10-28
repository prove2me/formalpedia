-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_choose_maximal_on_fixed_vertices
-- name    : WilliamsonShmoys.planar_completion_choose_maximal_on_fixed_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T02:25:54.952887+00:00
-- url     : https://prove2.me/theorems/82706d5f-fbd8-4659-a393-556840d730ad
-- title:
--   Choose a maximal drawable completion on the fixed vertex set
-- statement:
--   Every drawable graph on a finite fixed vertex set is contained in a drawable supergraph maximal under edge inclusion among drawable supergraphs on that same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_choose_maximal_on_fixed_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn L → L.edgeSet ⊆ K.edgeSet) := by sorry
