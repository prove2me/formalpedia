-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:25.346936+00:00
-- url     : https://prove2.me/theorems/fcf1b814-7848-4586-9efd-023714441148
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph on at least three finite vertices that has no drawable strict supergraph on those same vertices has exactly 3|V|−6 edges. The proposed independent route is to derive triangular faces from edge-maximality and then use Euler’s formula and face-edge incidence counting. The hypothesis n≥3 is retained, including the three-vertex boundary case; the unresolved core is formalizing that planar topology argument for HasPlanarDrawingOn.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count__p2m_9e7a2e08_df96_4db8_828f_8ffe40cd0bda_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U →
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) →
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       U.edgeFinset ⊆ T.edgeFinset)) :
    letI : DecidableRel T.Adj := dT
    T.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
