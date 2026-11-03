-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_lower_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
-- name    : WilliamsonShmoys.edge_maximal_planarDrawingOn_lower_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:31.022947+00:00
-- url     : https://prove2.me/theorems/bfa78551-440c-46c3-a993-a460d980df6b
-- title:
--   Edge lower bound for a maximal planar drawing
-- statement:
--   An edge-maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3|V|−6 edges. Prove maximality forces the graph to be connected and every face of a planar embedding to be triangular; Euler’s formula then gives the bound. For n=3, the only maximal planar graph is K₃, meeting the bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planarDrawingOn_lower_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V)
    (hmaximal : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; H.edgeFinset ⊆ K.edgeFinset) →
      HasPlanarDrawingOn K →
      (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; K.edgeFinset = H.edgeFinset)) :
    (letI : DecidableRel H.Adj := dH; 3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by sorry
