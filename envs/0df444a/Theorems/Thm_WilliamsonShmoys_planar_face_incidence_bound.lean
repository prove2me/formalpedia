-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_incidence_bound
-- name    : WilliamsonShmoys.planar_face_incidence_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:20:02.367792+00:00
-- url     : https://prove2.me/theorems/fd674c06-a657-4ca8-b75f-41f75c897817
-- title:
--   Face boundary incidence bound for a simple planar graph
-- statement:
--   For a connected simple graph with at least three vertices and a planar drawing, any face count satisfying Euler’s formula obeys 3F ≤ 2|E|. Prove this by representing face boundaries as walks: their directed edge sides partition the 2|E| incidences, and connectedness, simplicity, and the vertex lower bound exclude face boundaries of length below three. A bridge contributes both of its sides.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_incidence_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hconn : K.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∀ F : ℕ, Fintype.card V + F = K.edgeSet.ncard + 2 →
      3 * F <= 2 * K.edgeSet.ncard := by sorry
