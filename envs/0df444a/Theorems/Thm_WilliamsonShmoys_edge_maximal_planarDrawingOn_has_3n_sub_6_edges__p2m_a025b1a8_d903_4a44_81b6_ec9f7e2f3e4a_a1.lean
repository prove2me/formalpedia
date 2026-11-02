-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_has_3n_sub_6_edges__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
-- name    : WilliamsonShmoys.edge_maximal_planarDrawingOn_has_3n_sub_6_edges__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:58.483233+00:00
-- url     : https://prove2.me/theorems/4f160dcf-31cc-41b6-9e73-2a2d16cdab21
-- title:
--   Count edges in an edge-maximal planar drawing
-- statement:
--   A finite simple graph with at least three vertices that has a crossing-free drawing and is maximal under planar edge addition has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planarDrawingOn_has_3n_sub_6_edges__p2m_a025b1a8_d903_4a44_81b6_ec9f7e2f3e4a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V)
    (hmaximal : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; H.edgeFinset ⊆ K.edgeFinset) →
      HasPlanarDrawingOn K →
      (letI : DecidableRel H.Adj := dH; letI : DecidableRel K.Adj := dK; K.edgeFinset = H.edgeFinset)) :
    (letI : DecidableRel H.Adj := dH; H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
