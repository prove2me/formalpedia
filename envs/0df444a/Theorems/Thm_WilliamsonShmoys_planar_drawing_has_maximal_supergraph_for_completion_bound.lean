-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_completion_bound
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_completion_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:45:54.443315+00:00
-- url     : https://prove2.me/theorems/da921bf2-7fed-41a1-8011-b895b793fc89
-- title:
--   Maximal planar extension on the same vertex set
-- statement:
--   Every finitely supported graph with a drawing in the attached sense has a planar supergraph on the same vertex type that is maximal under edge inclusion. The boundary cases are covered: the original graph itself is an admissible candidate, and the finite set of simple graphs on V has an inclusion-maximal drawable member among those extending H. This removes the augmentation step from the parent. A proof route is to form that finite nonempty family and take a maximal element; finiteness makes this separate from the topological edge-count argument. The remaining detail is showing that the family and order are formalized with the exact edge-set inclusion predicates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_completion_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊂ L.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
