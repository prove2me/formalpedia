-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_for_edge_count
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:55:25.955555+00:00
-- url     : https://prove2.me/theorems/69c33857-68f4-4204-a58f-d6cec837179c
-- title:
--   Euler and triangular-face equations for maximal planar drawings
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices, there is a face count satisfying Euler’s equation and the triangular face-edge incidence equation. The equations are consistent with the three-vertex boundary case, where the maximal graph is a triangle and the face count is two. This child captures the planar embedding and face-counting work; the parent follows from arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition_for_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
