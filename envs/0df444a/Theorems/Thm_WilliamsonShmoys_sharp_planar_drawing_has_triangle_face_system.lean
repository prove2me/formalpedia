-- Prove2me | Theorems.Thm_WilliamsonShmoys_sharp_planar_drawing_has_triangle_face_system
-- name    : WilliamsonShmoys.sharp_planar_drawing_has_triangle_face_system
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:38:56.889586+00:00
-- url     : https://prove2.me/theorems/ed510285-de4a-4925-bf4b-20763941ea8f
-- title:
--   Sharp planar drawing yields a triangular face system
-- statement:
--   A finite simple graph on at least three vertices with the given planar drawing and sharp planar edge count has a multiset of three-vertex cliques such that every graph edge lies in exactly two members.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

theorem WilliamsonShmoys.sharp_planar_drawing_has_triangle_face_system
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hedge : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ faces : Multiset (Finset V),
      (∀ f, f ∈ faces → f.card = 3) ∧
      (∀ f, f ∈ faces → ∀ u, u ∈ f → ∀ v, v ∈ f →
        u ≠ v → H.Adj u v) ∧
      (∀ u v, H.Adj u v →
        (faces.filter (fun f => u ∈ f ∧ v ∈ f)).card = 2) := by
  sorry
