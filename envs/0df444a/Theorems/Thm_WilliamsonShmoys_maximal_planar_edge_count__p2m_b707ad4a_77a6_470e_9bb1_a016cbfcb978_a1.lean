-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:57:33.718351+00:00
-- url     : https://prove2.me/theorems/f0b6b169-74af-4776-af38-cf20fc29acd0
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable strict supergraph on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L → L.edgeSet = K.edgeSet) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
