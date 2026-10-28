-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_walks_282b0fbb
-- name    : WilliamsonShmoys.planar_drawing_face_walks_282b0fbb
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T10:42:37.801022+00:00
-- url     : https://prove2.me/theorems/544600dd-e0ba-49b1-81b4-ca17c3c23d9c
-- title:
--   Facial boundary walks from a planar drawing
-- statement:
--   A connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a finite list of facial boundary-walk lengths. Their count satisfies Euler’s formula, their total length is twice the number of edges (including both sides of bridges), and every length is at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_face_walks_282b0fbb
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 <= Fintype.card V)
    (hConnected : L.Connected) :
    ∃ faces : List ℕ,
      (Fintype.card V : Int) - (L.edgeSet.ncard : Int) + (faces.length : Int) = 2 ∧
      faces.sum = 2 * L.edgeSet.ncard ∧
      ∀ f, f ∈ faces → 3 <= f := by sorry
