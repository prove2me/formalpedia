-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1
-- name    : WilliamsonShmoys.planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:43.519241+00:00
-- url     : https://prove2.me/theorems/43831d01-c2a2-47cc-baf7-12299ab7bdf8
-- title:
--   Augment a planar graph to a triangulation
-- statement:
--   Every graph on a finite linearly ordered vertex type with at least three vertices that admits the specified planar drawing is a subgraph of a planar graph on the same vertices having exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_triangulation__p2m_75785758_9f27_4736_ab49_77b09febfcc3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    ∃ H : SimpleGraph V, K <= H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V = H.edgeSet.ncard + 6 := by sorry
