-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:51.502289+00:00
-- url     : https://prove2.me/theorems/1625d03f-5f98-459a-8070-43608692433f
-- title:
--   A maximal finite planar graph has the triangulation edge count
-- statement:
--   A drawable finite simple graph on at least three vertices that has no proper drawable supergraph on the same vertex set has exactly 3|V|−6 edges. This removes the topological triangulation and Euler-count argument from the parent. A proof route is to show maximality forces every face of the drawing to be triangular, then apply Euler’s formula; the hypothesis includes the three-vertex equality boundary. The remaining core obligation is formalizing those face and Euler arguments for the attached continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_supergraph__p2m_1b95303a_4f95_40e4_980b_ac53e8480e68_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hK : HasPlanarDrawingOn K) (hcard : 3 ≤ Fintype.card V) (hmax : ∀ (L : SimpleGraph V) [DecidableRel L.Adj], K ≤ L → HasPlanarDrawingOn L → L = K) : 3 * Fintype.card V = K.edgeFinset.card + 6 := by sorry
