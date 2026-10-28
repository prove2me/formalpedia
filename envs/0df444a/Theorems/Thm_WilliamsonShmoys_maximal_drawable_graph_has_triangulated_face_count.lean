-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_triangulated_face_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_triangulated_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:13:08.974932+00:00
-- url     : https://prove2.me/theorems/85360098-dba7-4c11-ba84-e51ff8660a8a
-- title:
--   Face counts of a maximal drawable graph
-- statement:
--   A maximal drawable simple graph on at least three vertices has a finite face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_has_triangulated_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hmax : ∀ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T →
      R ≤ T → T = R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = R.edgeSet.ncard + 2 ∧
      3 * f = 2 * R.edgeSet.ncard := by sorry
