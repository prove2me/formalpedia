-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension_for_triangulation_extension
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T21:11:40.645206+00:00
-- url     : https://prove2.me/theorems/5e3eb316-051d-46e8-a1da-ca0b75c8a1d0
-- title:
--   Choose a maximal planar supergraph on the same vertices
-- statement:
--   Among the drawable supergraphs of the given finite graph on the same vertices, there is one maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension_for_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
