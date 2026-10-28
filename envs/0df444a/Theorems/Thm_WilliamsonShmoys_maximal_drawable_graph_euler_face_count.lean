-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_euler_face_count
-- name    : WilliamsonShmoys.maximal_drawable_graph_euler_face_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:03:35.193336+00:00
-- url     : https://prove2.me/theorems/2aa9d4d8-ca19-4a3e-94b2-47d01f3eb35e
-- title:
--   Euler face count for maximal drawable graphs
-- statement:
--   A maximal drawable simple graph on at least three vertices has a natural-number face count satisfying Euler’s equation. This isolates the Euler obligation; a proof can establish connectedness from maximality and apply Euler’s formula to the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 := by sorry
