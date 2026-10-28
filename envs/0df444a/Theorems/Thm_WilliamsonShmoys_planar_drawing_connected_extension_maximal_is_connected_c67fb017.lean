-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_maximal_is_connected_c67fb017
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_maximal_is_connected_c67fb017
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:41:04.825002+00:00
-- url     : https://prove2.me/theorems/9230e872-638d-4e23-b691-a1a34e154f54
-- title:
--   Maximal drawn planar extensions are connected
-- statement:
--   A maximal graph admitting the specified planar drawing is connected when the finite vertex type has at least three elements: otherwise one can add an edge between components while preserving the drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_maximal_is_connected_c67fb017
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.Connected := by
  sorry
