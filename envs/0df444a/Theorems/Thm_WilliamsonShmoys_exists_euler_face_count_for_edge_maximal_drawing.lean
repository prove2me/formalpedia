-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_euler_face_count_for_edge_maximal_drawing
-- name    : WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:00:17.425892+00:00
-- url     : https://prove2.me/theorems/ec75bbb7-38db-4926-916a-a6b72b574497
-- title:
--   Euler and face-incidence equations for a maximal planar drawing
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices, some natural number of faces satisfies Euler’s equation and the triangular-face incidence equation. Together these equations imply the edge count required by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_euler_face_count_for_edge_maximal_drawing {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧ 3 * f = 2 * L.edgeSet.ncard := by sorry
