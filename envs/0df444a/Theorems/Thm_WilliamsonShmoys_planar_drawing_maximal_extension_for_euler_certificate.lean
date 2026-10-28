-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_euler_certificate
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_for_euler_certificate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:27:05.928575+00:00
-- url     : https://prove2.me/theorems/a468ebaf-0e9c-45d9-9876-dcfd3d43a5da
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable finite graph on at least three vertices has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension_for_euler_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ J : SimpleGraph V,
        K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ K := by sorry
