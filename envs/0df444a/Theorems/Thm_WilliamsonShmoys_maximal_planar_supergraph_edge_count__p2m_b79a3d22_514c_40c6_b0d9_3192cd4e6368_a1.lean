-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:33:34.53914+00:00
-- url     : https://prove2.me/theorems/23689463-5c07-4e0b-a29b-546de8e1e4a9
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable finite simple graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_b79a3d22_514c_40c6_b0d9_3192cd4e6368_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (dL : DecidableRel L.Adj) (hL : HasPlanarDrawingOn L) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ (M : SimpleGraph V) (dM : DecidableRel M.Adj), L ≤ M → HasPlanarDrawingOn M → M ≤ L) : 3 * Fintype.card V = L.edgeFinset.card + 6 := by sorry
