-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_same_vertices_784d1fda_4529_43fd_94a5_bf399d6fa183
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_same_vertices_784d1fda_4529_43fd_94a5_bf399d6fa183
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:22:16.821787+00:00
-- url     : https://prove2.me/theorems/53384e13-a12f-4822-8e5e-d7f76a7ccbb5
-- title:
--   A planar drawing has a maximal supergraph on the same vertices
-- statement:
--   Every graph with a drawing has a supergraph on the same finite vertex type that has a drawing and is maximal among such supergraphs. This child provides inclusion and maximality; the parent’s edge-count hypothesis supplies strict inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_same_vertices_784d1fda_4529_43fd_94a5_bf399d6fa183
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    Exists (fun M : SimpleGraph V =>
      And (P.edgeSet ⊆ M.edgeSet)
      (And (WilliamsonShmoys.HasPlanarDrawingOn M)
        (forall R : SimpleGraph V,
          M.edgeSet ⊆ R.edgeSet ->
          WilliamsonShmoys.HasPlanarDrawingOn R ->
          R.edgeSet = M.edgeSet))) := by sorry
