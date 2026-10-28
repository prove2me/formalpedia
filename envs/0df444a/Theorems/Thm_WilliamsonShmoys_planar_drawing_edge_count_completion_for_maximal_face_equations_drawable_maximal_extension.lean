-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion_for_maximal_face_equations_drawable_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_drawable_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:48:51.836875+00:00
-- url     : https://prove2.me/theorems/468f5139-a89d-44ce-b6a3-48dbb7fc3954
-- title:
--   Finite edge-maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_completion_for_maximal_face_equations_drawable_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
