-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension_face_data
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T15:26:01.83257+00:00
-- url     : https://prove2.me/theorems/7d99246b-3de7-4fc1-9f5c-e84e3d014e64
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has an inclusion-maximal drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K → HasPlanarDrawingOn K → K = J := by sorry
