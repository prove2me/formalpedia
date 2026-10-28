-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_euler_face_equations_for_euler_count
-- name    : WilliamsonShmoys.maximal_drawable_euler_face_equations_for_euler_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:33:05.133262+00:00
-- url     : https://prove2.me/theorems/0d4c0c18-ee7e-4391-b415-6329287877bb
-- title:
--   Euler and triangular-face equations for a maximal drawable graph
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs has a face count satisfying Euler’s equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_euler_face_equations_for_euler_count {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → L = M) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧ 3 * f = 2 * L.edgeSet.ncard := by sorry
