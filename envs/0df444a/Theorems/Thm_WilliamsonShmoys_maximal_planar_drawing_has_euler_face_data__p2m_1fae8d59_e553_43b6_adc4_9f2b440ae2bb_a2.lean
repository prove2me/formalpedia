-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_face_data__p2m_1fae8d59_e553_43b6_adc4_9f2b440ae2bb_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_face_data__p2m_1fae8d59_e553_43b6_adc4_9f2b440ae2bb_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:13.810717+00:00
-- url     : https://prove2.me/theorems/7f938502-4ebe-49de-af5d-b80801e1f743
-- title:
--   Euler and face-incidence data for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has a face count satisfying Euler’s equation and the triangular-face incidence equation. Starting from the supplied arcs, a proof must construct the plane embedding, use maximality to rule out disconnectedness and nontriangular faces, and establish Euler’s formula and the two incidences per edge. This removes the geometric and topological obligation from the parent. The remaining core obligation is precisely that formalization from the arc predicates; in particular, the proof must handle facial boundary walks rather than assume faces are triangles.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_face_data__p2m_1fae8d59_e553_43b6_adc4_9f2b440ae2bb_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K' : SimpleGraph V, H ≤ K' → WilliamsonShmoys.HasPlanarDrawingOn K' → K' = H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    ∃ F : ℕ,
      Fintype.card V + F = H.edgeFinset.card + 2 ∧
      2 * H.edgeFinset.card = 3 * F := by
  sorry
