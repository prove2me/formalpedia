-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:25.923503+00:00
-- url     : https://prove2.me/theorems/42e17741-b5fb-4586-95ad-fdcb2ee9a443
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has exactly 3|V|−6 edges. This child isolates the topological and Euler-counting work. A proof route is to show maximality forces the drawing to be connected with triangular faces, then use Euler’s formula and count each edge twice along face boundaries; the three-vertex case is the triangle. The main remaining obligation is formalizing these drawing-to-face facts for the supplied arc-based definition, including disconnected graphs and cut vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hV : 3 ≤ Fintype.card V) (hmax : ∀ X : SimpleGraph V, W ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = W) : W.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
