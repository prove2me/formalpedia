-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_edge_maximal_supergraph__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
-- name    : WilliamsonShmoys.planarDrawingOn_has_edge_maximal_supergraph__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:55.819204+00:00
-- url     : https://prove2.me/theorems/e4912939-d225-4f8a-9884-0c3e2886e469
-- title:
--   Extend a planar drawing to an edge-maximal supergraph
-- statement:
--   Any finite simple graph with at least three vertices and a crossing-free drawing has a crossing-free supergraph on the same vertices that is maximal under edge inclusion among graphs admitting such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_has_edge_maximal_supergraph__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel G.Adj := dG; letI : DecidableRel H.Adj := dH; G.edgeFinset ⊆ H.edgeFinset) ∧
      HasPlanarDrawingOn H ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; H.edgeFinset ⊆ K.edgeFinset) →
        HasPlanarDrawingOn K →
        (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; K.edgeFinset = H.edgeFinset)) := by sorry
