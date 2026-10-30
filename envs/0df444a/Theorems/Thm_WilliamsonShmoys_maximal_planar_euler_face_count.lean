-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_face_count
-- name    : WilliamsonShmoys.maximal_planar_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:19:09.651698+00:00
-- url     : https://prove2.me/theorems/367e7ff6-f47c-4801-a657-f77b95acb1d0
-- title:
--   Euler face count for a maximal planar drawing
-- statement:
--   For a maximal drawable simple graph on at least three vertices, Euler's formula gives a face count f satisfying |V| + f = |E| + 2. Maximality implies connectedness; a proof can translate the drawing into a cyclic-order map and apply Euler's formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J = H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
