-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_edge_count
-- name    : WilliamsonShmoys.planar_triangulation_maximal_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:54:49.152984+00:00
-- url     : https://prove2.me/theorems/c132589d-1617-4a78-a962-6da5cb0b051f
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on its vertex set has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_maximal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hDraw : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      (∀ u v, L.Adj u v → M.Adj u v) →
      HasPlanarDrawingOn M →
      ∀ u v, M.Adj u v → L.Adj u v) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
