-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_maximal_edge_lower
-- name    : WilliamsonShmoys.maximal_planar_face_count_maximal_edge_lower
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:28:50.679799+00:00
-- url     : https://prove2.me/theorems/f39411d7-0b3e-4923-9f24-5e532efa7cda
-- title:
--   Maximal planar edge lower bound for the face count theorem
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_maximal_edge_lower
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
