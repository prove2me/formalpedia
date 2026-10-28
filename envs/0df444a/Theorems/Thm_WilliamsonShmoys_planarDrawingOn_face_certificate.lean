-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_face_certificate
-- name    : WilliamsonShmoys.planarDrawingOn_face_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:39:07.095283+00:00
-- url     : https://prove2.me/theorems/2c5fb816-1874-498b-ac22-d885021226e5
-- title:
--   Finite face certificate for a connected planar drawing
-- statement:
--   A connected graph with at least three vertices and a crossing-free drawing has a positive finite face count satisfying Euler’s relation; its face-boundary lengths sum to twice the number of edges, and every face boundary has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.planarDrawingOn_face_certificate
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hConnected : L.Connected)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (F : ℕ) (faceLength : Fin F → ℕ),
      0 < F ∧
      Fintype.card V + F = L.edgeSet.ncard + 2 ∧
      (∑ i : Fin F, faceLength i) = 2 * L.edgeSet.ncard ∧
      ∀ i, 3 ≤ faceLength i := by
  sorry
