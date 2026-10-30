-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_equations_for_bound
-- name    : WilliamsonShmoys.maximal_planar_euler_face_equations_for_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T10:31:42.681987+00:00
-- url     : https://prove2.me/theorems/a91ff678-2584-4a25-8e60-fb94ad6b5c72
-- title:
--   Euler and face-count equations for maximal planar drawings
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set, there is a face count f satisfying Euler’s equation and the triangular face-edge incidence equation. Together these equations imply the target edge bound. The case of exactly three vertices is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_euler_face_equations_for_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hMax : ∀ J : SimpleGraph V, K ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J = K)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
