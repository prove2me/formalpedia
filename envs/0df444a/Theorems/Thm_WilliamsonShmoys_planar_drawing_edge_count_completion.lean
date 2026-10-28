-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_completion
-- name    : WilliamsonShmoys.planar_drawing_edge_count_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T01:27:37.262857+00:00
-- url     : https://prove2.me/theorems/de4e179e-7e15-49c6-90b8-ccb0d05047fd
-- title:
--   Complete a planar drawing to the maximal edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable graph on the same vertices whose edge count is exactly 3|V|−6; the completion’s edge count bounds the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      N.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by sorry
