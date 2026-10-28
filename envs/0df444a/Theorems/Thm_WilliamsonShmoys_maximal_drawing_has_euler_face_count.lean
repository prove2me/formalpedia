-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_euler_face_count
-- name    : WilliamsonShmoys.maximal_drawing_has_euler_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T03:17:57.360074+00:00
-- url     : https://prove2.me/theorems/42d00589-7559-46d8-b4d4-b10a96c04726
-- title:
--   Maximal drawable graphs have an Euler face count
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has a face count satisfying Euler's equation and the triangular face-edge incidence equation. This child isolates the topological work: establish connectedness and triangular faces from maximality, then apply the planar Euler and incidence formulas.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawing_has_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
