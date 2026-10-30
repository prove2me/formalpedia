-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_face_equations_87a22553
-- name    : WilliamsonShmoys.maximal_drawable_face_equations_87a22553
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T14:01:28.893881+00:00
-- url     : https://prove2.me/theorems/2d3cd752-b63f-4ced-b91f-a6fd995df2ca
-- title:
--   Euler and face-incidence equations for a maximal drawable graph
-- statement:
--   For a maximal drawable graph with at least three vertices, the number of vertices plus the number of faces equals the number of edges plus two, and counting sides of triangular faces gives three times the number of faces equal to twice the number of edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_face_equations_87a22553 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) : ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f = 2 * H.edgeSet.ncard := by sorry
