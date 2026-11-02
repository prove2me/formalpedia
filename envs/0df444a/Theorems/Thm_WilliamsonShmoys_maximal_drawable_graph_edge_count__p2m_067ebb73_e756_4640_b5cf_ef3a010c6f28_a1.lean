-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:32.970486+00:00
-- url     : https://prove2.me/theorems/80c37abd-a278-4e21-90d9-d42081afbb20
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable graph on at least three finite vertices that has maximum edge count among its drawable supergraphs has exactly 3|V|−6 edges. This isolates the geometric and Euler-counting work from the parent. A proof route is to show maximality rules out disconnected components and any face with more than three boundary edges, so the embedding is a triangulation, and then apply Euler’s formula. The disconnected and small-order cases must be handled under the stated |V| ≥ 3 hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hR : HasPlanarDrawingOn R)
    (hMax : ∀ S : SimpleGraph V, (∀ u v, R.Adj u v → S.Adj u v) →
      HasPlanarDrawingOn S →
      (letI : DecidableRel S.Adj := Classical.decRel S.Adj
       letI : DecidableRel R.Adj := Classical.decRel R.Adj
       S.edgeFinset.card ≤ R.edgeFinset.card)) :
    (letI : DecidableRel R.Adj := Classical.decRel R.Adj
     R.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
