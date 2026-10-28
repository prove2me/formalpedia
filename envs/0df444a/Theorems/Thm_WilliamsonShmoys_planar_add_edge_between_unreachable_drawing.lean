-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_unreachable_drawing
-- name    : WilliamsonShmoys.planar_add_edge_between_unreachable_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:16:25.45445+00:00
-- url     : https://prove2.me/theorems/e5aa426e-598c-4d11-af3b-d931b1b9f6c6
-- title:
--   Draw the graph with exactly one bridge added
-- statement:
--   For unreachable vertices u and v in a graph with a crossing-free drawing, construct a crossing-free drawing of the graph whose edges are exactly the original edges plus uv.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_unreachable_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (hUV : ¬ K.Reachable u v) :
    ∃ L : SimpleGraph V,
      (∀ a b, L.Adj a b ↔ K.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
