-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulated_completion
-- name    : WilliamsonShmoys.planar_drawing_triangulated_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:44:40.929729+00:00
-- url     : https://prove2.me/theorems/9af09745-c44b-49e2-8eae-92b868399a58
-- title:
--   Triangulated completion of a connected planar drawing
-- statement:
--   Every connected finite simple graph with a crossing-free drawing and at least three vertices can be extended, on the same vertex set, to a graph with a crossing-free drawing and exactly 3n−6 edges; the original edge count is no larger than the completed graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulated_completion
    {α : Type} [Fintype α] [LinearOrder α]
    (G : SimpleGraph α)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (n : Nat)
    (hLarge : 3 ≤ n)
    (hcard : Fintype.card α = n) :
    ∃ K : SimpleGraph α,
      G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * n - 6 := by sorry
