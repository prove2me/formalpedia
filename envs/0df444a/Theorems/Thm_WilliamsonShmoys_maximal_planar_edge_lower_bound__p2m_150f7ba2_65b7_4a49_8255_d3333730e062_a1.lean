-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:43:40.267217+00:00
-- url     : https://prove2.me/theorems/7ffdcecf-da07-45cb-a4da-fb98455db8ef
-- title:
--   Edge lower bound for maximal planar graphs
-- statement:
--   A finite simple graph on at least three vertices that is maximal among planar supergraphs on its vertex type has at least 3|V|−6 edges. This is the topological core left after the parent’s finite maximality step. A proof route is to derive connectedness and triangular faces for a maximal planar embedding, then apply Euler’s formula and count face-edge incidences; the condition of at least three vertices is essential to the usual bound. The parent combines this result with the preceding lemma. Formalizing the arc-based drawing predicate and its relation to faces/Euler counting remains the main obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_150f7ba2_65b7_4a49_8255_d3333730e062_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ L : SimpleGraph V,
      (∀ u v, G.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = G) :
    3 * Fintype.card V ≤ G.edgeSet.ncard + 6 := by sorry
