-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_spanning_connected_extension
-- name    : WilliamsonShmoys.planar_drawing_spanning_connected_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:45:50.621969+00:00
-- url     : https://prove2.me/theorems/397c4eb7-7155-4bc0-b8ca-57f1ddf01afa
-- title:
--   Connect a nonempty planar drawing by adding edges
-- statement:
--   For a planar drawing on at least three vertices, one can add edges without changing the vertex set to obtain a connected planar graph. The positive count `c` records that the extension adds `c - 1` edges, and all original edges remain.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_spanning_connected_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ (c : ℕ) (K : SimpleGraph V),
      1 ≤ c ∧
      K.Connected ∧
      HasPlanarDrawingOn K ∧
      (∀ ⦃u v : V⦄, L.Adj u v → K.Adj u v) ∧
      L.edgeSet.ncard + c = K.edgeSet.ncard + 1 := by sorry
