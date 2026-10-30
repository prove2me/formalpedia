-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound
-- name    : WilliamsonShmoys.planar_simple_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T01:19:25.019671+00:00
-- url     : https://prove2.me/theorems/b62bf6b9-6c33-4a67-bfba-22014aea8916
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most 3V − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
