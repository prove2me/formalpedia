-- Prove2me | Theorems.Thm_maximal_planar_drawing_edge_bound
-- name    : maximal_planar_drawing_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:15:07.118959+00:00
-- url     : https://prove2.me/theorems/88a0414f-c61f-40ae-b394-72290e214dab
-- title:
--   Euler edge bound for a maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices whose drawing admits no proper planar supergraph satisfies the classical Euler edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem maximal_planar_drawing_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
