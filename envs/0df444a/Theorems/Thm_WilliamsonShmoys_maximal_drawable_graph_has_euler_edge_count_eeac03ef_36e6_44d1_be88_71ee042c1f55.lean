-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_has_euler_edge_count_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- name    : WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:56:54.075966+00:00
-- url     : https://prove2.me/theorems/017f62cf-0478-4db2-9238-3ddddcc3c0c0
-- title:
--   A maximal drawable graph has the planar maximum edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly `3n - 6` edges. A proof route is to establish that maximality forces connectedness and triangular faces in the drawing, then use Euler's formula and face-edge incidence counting. The three-vertex case yields the triangle. Formalizing the geometric steps for `HasPlanarDrawingOn` is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_eeac03ef_36e6_44d1_be88_71ee042c1f55 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
