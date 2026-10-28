-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound
-- name    : WilliamsonShmoys_maximal_planar_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T04:43:00.08147+00:00
-- url     : https://prove2.me/theorems/c14b33c7-7ac0-4523-9527-a266159a5caa
-- title:
--   Edge bound for maximal planar graphs
-- statement:
--   A graph on at least three vertices that has a crossing-free drawing and admits no proper planar supergraph on the same vertex set has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys_maximal_planar_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
