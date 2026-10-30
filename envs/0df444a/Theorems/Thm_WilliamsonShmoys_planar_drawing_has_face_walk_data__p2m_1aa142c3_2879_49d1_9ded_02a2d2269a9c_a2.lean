-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_face_walk_data__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
-- name    : WilliamsonShmoys.planar_drawing_has_face_walk_data__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T09:33:42.931302+00:00
-- url     : https://prove2.me/theorems/718f82d4-ed98-4545-860f-afb32055363d
-- title:
--   Euler facial-walk data from a planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the specified planar drawing has facial boundary-walk lengths satisfying Euler’s formula, summing to twice the number of edges, with each length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_face_walk_data__p2m_1aa142c3_2879_49d1_9ded_02a2d2269a9c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnected : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ faceLengths : List ℕ,
      faceLengths.length = H.edgeSet.ncard - Fintype.card V + 2 ∧
      faceLengths.sum = 2 * H.edgeSet.ncard ∧
      ∀ ℓ ∈ faceLengths, 3 ≤ ℓ := by sorry
