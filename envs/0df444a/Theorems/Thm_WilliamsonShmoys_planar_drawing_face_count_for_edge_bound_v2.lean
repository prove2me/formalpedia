-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count_for_edge_bound_v2
-- name    : WilliamsonShmoys.planar_drawing_face_count_for_edge_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T01:51:13.471005+00:00
-- url     : https://prove2.me/theorems/51a9b3eb-dda2-461c-a497-8e5607f1fe5f
-- title:
--   Euler face count and incidence bound for a planar drawing
-- statement:
--   A connected simple graph with at least three vertices and the specified crossing-free drawing has a natural-number face count satisfying Euler’s relation and the face-edge incidence bound. The minimum vertex count is retained because the incidence argument relies on the absence of face-boundary walks of length one or two in this setting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count_for_edge_bound_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hConnected : L.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = L.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by sorry
