-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:21:42.769436+00:00
-- url     : https://prove2.me/theorems/3a2a40ac-ecda-4b50-94dd-d355e6a5bd05
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has a face count satisfying Euler’s equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_equations_for_edge_count_9ae33b99_f9c7_42b4_990c_c6c34d566138
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
