-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_edge_maximal_supergraph__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
-- name    : WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:43:01.2686+00:00
-- url     : https://prove2.me/theorems/15de7f60-3f94-44ed-9413-540d275804dc
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph T has a drawable supergraph U on the same finite vertex type that contains T and admits no drawable supergraph with strictly more edges. This follows by maximizing edge count over the finite family of simple graphs on V that contain T and have a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_edge_maximal_supergraph__p2m_59f689b9_056b_46e8_a00d_961751c5f3da_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V) (dT : DecidableRel T.Adj)
    (hT : HasPlanarDrawingOn T)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (U : SimpleGraph V) (dU : DecidableRel U.Adj),
      HasPlanarDrawingOn U ∧
      (letI : DecidableRel T.Adj := dT
       letI : DecidableRel U.Adj := dU
       T.edgeFinset ⊆ U.edgeFinset) ∧
      (∀ (W : SimpleGraph V) (dW : DecidableRel W.Adj),
        letI : DecidableRel U.Adj := dU
        letI : DecidableRel W.Adj := dW
        HasPlanarDrawingOn W →
        U.edgeFinset ⊆ W.edgeFinset →
        W.edgeFinset = U.edgeFinset) := by sorry
