-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:47.90824+00:00
-- url     : https://prove2.me/theorems/710ae9cd-06e1-4ca5-a820-3c02fa6bdb35
-- title:
--   Edge bound for an edge-maximal drawable graph
-- statement:
--   A finite drawable simple graph on at least three vertices that is maximal under drawable edge-set inclusion has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_c643eab9_16cc_4e69_8d73_dd1e68fa5bd2_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, HasPlanarDrawingOn K →
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset ⊆ K.edgeFinset → K.edgeFinset ⊆ H.edgeFinset))
    (hcard : 3 ≤ Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by sorry
