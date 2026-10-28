-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T13:57:08.511288+00:00
-- url     : https://prove2.me/theorems/2218dce2-1198-4abc-9cb0-bb5b50a2d3f4
-- title:
--   Euler and face-incidence equations for a maximal planar drawing
-- statement:
--   For a maximal drawable simple graph with at least three vertices, a face count satisfies Euler’s equation and the incidence equation for triangular faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition_edge_bound_9a40956c04dd448b9ab680f8d2edf7ce
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by
  sorry
