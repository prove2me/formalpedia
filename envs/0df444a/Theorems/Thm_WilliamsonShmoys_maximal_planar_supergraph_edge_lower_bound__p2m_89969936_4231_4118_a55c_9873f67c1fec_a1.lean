-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_lower_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:13:57.261205+00:00
-- url     : https://prove2.me/theorems/09ee00d6-d6e0-4e98-aab0-c4cdc0b16fb7
-- title:
--   Lower edge bound for a maximal drawable supergraph
-- statement:
--   If L is drawable and maximal among drawable supergraphs of K on the same finite vertex type, with at least three vertices, then L has at least 3|V|−6 edges. The proof route is to establish that maximality forces a triangulation, then apply Euler’s formula and face-edge incidence counting; the cases of disconnected or non-2-connected L must be handled as part of that argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_lower_bound__p2m_89969936_4231_4118_a55c_9873f67c1fec_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hmax :
      (letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
        fun G => Classical.decRel G.Adj
       K.edgeFinset ⊆ L.edgeFinset ∧
       HasPlanarDrawingOn L ∧
       ∀ M : SimpleGraph V,
         L.edgeFinset ⊆ M.edgeFinset →
         HasPlanarDrawingOn M →
         M.edgeFinset = L.edgeFinset)) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by sorry
