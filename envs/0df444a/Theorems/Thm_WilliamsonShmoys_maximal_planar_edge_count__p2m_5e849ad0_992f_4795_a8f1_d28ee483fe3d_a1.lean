-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:42:39.986491+00:00
-- url     : https://prove2.me/theorems/1cedfa43-e759-4304-8f59-175ee0ad0ade
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   If a drawable graph on at least three vertices has no drawable strict supergraph on the same vertex type, then it has exactly 3|V|−6 edges. A proof route is to establish that maximality forces triangular faces and then use Euler’s formula. This is the topological core of the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5e849ad0_992f_4795_a8f1_d28ee483fe3d_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hMax : ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
