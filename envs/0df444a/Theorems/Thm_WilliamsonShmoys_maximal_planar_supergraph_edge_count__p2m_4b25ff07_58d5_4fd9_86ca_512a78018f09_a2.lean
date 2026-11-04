-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:20.925927+00:00
-- url     : https://prove2.me/theorems/89969936-4231-4118-a55c-9873f67c1fec
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   If L is drawable and maximal among drawable supergraphs containing K on the same finite vertex set, and the vertex count is at least three, then L has exactly 3|V|−6 edges. The proof must show that maximality forces a triangulated planar embedding and then use Euler’s formula and face-edge incidence counting. The lower bound on the number of vertices is necessary, with |V| = 3 included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_4b25ff07_58d5_4fd9_86ca_512a78018f09_a2
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
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
