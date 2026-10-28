-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_same_vertex_set_for_target_957bde25
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_same_vertex_set_for_target_957bde25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:06:54.879063+00:00
-- url     : https://prove2.me/theorems/ccca2255-a9cf-44f3-b771-3aa3d223a154
-- title:
--   Choose a maximal drawable extension on the same vertex set
-- statement:
--   Among the finitely many simple graphs on the given vertex type that contain K and admit a drawing, choose one maximal under inclusion. This removes the finite selection step from the parent; an independent route is to maximize edgeSet.ncard over that finite nonempty family and show any drawable strict supergraph has more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_same_vertex_set_for_target_957bde25
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    exists L : SimpleGraph V,
      K <= L /\
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      (forall M : SimpleGraph V, L <= M -> WilliamsonShmoys.HasPlanarDrawingOn M -> M = L) := by sorry
