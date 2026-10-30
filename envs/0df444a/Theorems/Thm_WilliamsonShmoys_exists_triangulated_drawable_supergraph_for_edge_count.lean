-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_drawable_supergraph_for_edge_count
-- name    : WilliamsonShmoys.exists_triangulated_drawable_supergraph_for_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:31:47.217895+00:00
-- url     : https://prove2.me/theorems/0d58a30b-b602-48eb-8495-a2236e2d87f2
-- title:
--   Augment a drawable graph to a triangulated supergraph
-- statement:
--   Every drawable finite simple graph with at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. This packages planar augmentation to a maximal triangulation together with the Euler-formula edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_drawable_supergraph_for_edge_count {V : Type} [Fintype V] [LinearOrder V] (S : SimpleGraph V) (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S) (hCard : 3 ≤ Fintype.card V) : ∃ T : SimpleGraph V, S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧ 3 * Fintype.card V = T.edgeSet.ncard + 6 := by sorry
