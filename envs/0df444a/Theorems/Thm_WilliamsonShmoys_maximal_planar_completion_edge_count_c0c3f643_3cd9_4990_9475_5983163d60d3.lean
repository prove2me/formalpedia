-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_edge_count_c0c3f643_3cd9_4990_9475_5983163d60d3
-- name    : WilliamsonShmoys.maximal_planar_completion_edge_count_c0c3f643_3cd9_4990_9475_5983163d60d3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T05:56:26.149698+00:00
-- url     : https://prove2.me/theorems/b24ee22a-ee0a-4874-a748-da2528ed7758
-- title:
--   Triangulated planar completion on the same vertex set
-- statement:
--   Every graph with the specified crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_completion_edge_count_c0c3f643_3cd9_4990_9475_5983163d60d3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
