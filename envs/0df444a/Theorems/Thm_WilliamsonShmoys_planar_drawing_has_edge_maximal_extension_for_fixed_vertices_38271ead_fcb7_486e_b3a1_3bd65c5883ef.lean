-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_extension_for_fixed_vertices_38271ead_fcb7_486e_b3a1_3bd65c5883ef
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_for_fixed_vertices_38271ead_fcb7_486e_b3a1_3bd65c5883ef
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:59:30.674254+00:00
-- url     : https://prove2.me/theorems/7041b494-b251-43f3-a160-ae161fc62ef0
-- title:
--   A drawable graph has a maximal drawable extension on its fixed vertices
-- statement:
--   Every drawable graph on a finite vertex type has an inclusion-maximal drawable supergraph on the same vertices. This removes the finite maximal-choice step from the parent. It has no lower bound on the vertex count because maximality exists even for smaller graphs. A direct proof orders the finite set of supergraphs of `N`, restricts to those with a planar drawing, and selects a maximal element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_extension_for_fixed_vertices_38271ead_fcb7_486e_b3a1_3bd65c5883ef
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ K : SimpleGraph V,
        M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ M := by sorry
