-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_connected_induced_bounds__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
-- name    : WilliamsonShmoys.planar_edge_bound_from_connected_induced_bounds__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:34:42.554202+00:00
-- url     : https://prove2.me/theorems/d560826c-2a6b-46ec-826e-191525151789
-- title:
--   Planar edge bound from connected induced subgraphs
-- statement:
--   If every connected induced subgraph on at least three vertices satisfies the planar edge bound, then the whole finite simple graph satisfies it, provided the whole graph has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_connected_induced_bounds__p2m_ac18a95b_13f8_4a76_980e_021bef74dbe9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hcard : 3 <= Fintype.card V)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry
