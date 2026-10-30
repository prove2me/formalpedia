-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_completion_44ee6346_c5c8_4937_ab77_ca51e02cb099
-- name    : WilliamsonShmoys.planar_edge_count_completion_44ee6346_c5c8_4937_ab77_ca51e02cb099
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:33:42.146794+00:00
-- url     : https://prove2.me/theorems/9997c086-4955-4a2d-b111-8f7e91953844
-- title:
--   Completion of a planar drawing to the maximal planar edge count
-- statement:
--   Any graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertices with exactly 3|V|−6 edges. At |V| = 3, this permits completion to the triangle. The result supplies the target’s completion step; it does not assert that the original graph already has this edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_completion_44ee6346_c5c8_4937_ab77_ca51e02cb099
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      Set.Subset G.edgeSet H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
