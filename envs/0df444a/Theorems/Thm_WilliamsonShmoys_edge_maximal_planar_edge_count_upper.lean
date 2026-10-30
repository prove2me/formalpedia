-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_edge_count_upper
-- name    : WilliamsonShmoys.edge_maximal_planar_edge_count_upper
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:33:59.931679+00:00
-- url     : https://prove2.me/theorems/8b83d883-b630-4752-965c-607725d24ab6
-- title:
--   Upper edge bound for a finite simple planar graph
-- statement:
--   A finite simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the planar edge bound, obtained from Euler's formula and face-edge incidence counting, with disconnected graphs handled componentwise.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_edge_count_upper
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
