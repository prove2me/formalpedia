-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_triangulation_completion
-- name    : WilliamsonShmoys.planar_drawing_on_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:30:34.172521+00:00
-- url     : https://prove2.me/theorems/4139d98a-55a9-4e11-a4e0-b8bd2067f3f0
-- title:
--   Complete a planar drawing to a triangulation
-- statement:
--   Any planar drawing on at least three vertices can be extended, without adding vertices, to a planar graph with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_on_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by sorry
