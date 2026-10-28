-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion_exists_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_triangulated_completion_exists_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:05:23.563032+00:00
-- url     : https://prove2.me/theorems/4a5efcf7-4e17-4a7d-85d5-dc803e3f3182
-- title:
--   Maximal planar extension on the same vertex type
-- statement:
--   A graph with a planar drawing on a finite ordered vertex type has a planar supergraph on that same type that is maximal among planar supergraphs under graph inclusion. Maximize the edge set over the finite nonempty family of such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_completion_exists_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
