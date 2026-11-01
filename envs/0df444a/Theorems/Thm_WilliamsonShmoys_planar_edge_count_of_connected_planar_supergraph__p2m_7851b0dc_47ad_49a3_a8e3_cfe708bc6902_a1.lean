-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_of_connected_planar_supergraph__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
-- name    : WilliamsonShmoys.planar_edge_count_of_connected_planar_supergraph__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:33.284197+00:00
-- url     : https://prove2.me/theorems/512bd221-ca2d-4baf-bc2f-a3776007344e
-- title:
--   Transfer the connected planar edge bound to a subgraph
-- statement:
--   If every connected planar graph on the finite vertex type obeys the edge bound, then any planar graph that has a connected planar supergraph on the same vertices obeys the bound too. The proof applies the connected bound to the supergraph and uses monotonicity of edge count under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_of_connected_planar_supergraph__p2m_7851b0dc_47ad_49a3_a8e3_cfe708bc6902_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hconnBound : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      H.Connected → HasPlanarDrawingOn H → 3 ≤ Fintype.card V →
      (letI : DecidableRel H.Adj := dH
       H.edgeFinset.card ≤ 3 * Fintype.card V - 6))
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V)
    (hcomplete : ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      G ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H) :
    (letI : DecidableRel G.Adj := dG
     G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
