-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_completion_face_count_6e15fe35
-- name    : WilliamsonShmoys.triangulation_completion_face_count_6e15fe35
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:25:56.986896+00:00
-- url     : https://prove2.me/theorems/8dd4263a-69fd-4b40-9e27-a11745f2ccef
-- title:
--   Euler and triangular-face counts for a maximal drawing
-- statement:
--   For a maximal drawable simple graph with at least three vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_completion_face_count_6e15fe35
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → M = N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
