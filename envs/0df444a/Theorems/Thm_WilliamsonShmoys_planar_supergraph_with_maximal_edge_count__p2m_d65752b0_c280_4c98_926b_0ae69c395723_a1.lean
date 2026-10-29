-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:51:02.657064+00:00
-- url     : https://prove2.me/theorems/8211ed91-b53b-462c-a828-870a3303abaf
-- title:
--   Planar supergraph with maximal edge count
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_with_maximal_edge_count__p2m_d65752b0_c280_4c98_926b_0ae69c395723_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
