-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_card_upper_bound__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_card_upper_bound__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:54:38.698031+00:00
-- url     : https://prove2.me/theorems/01732aef-dd3e-4b78-a11c-771f0411d541
-- title:
--   Edge bound for a drawable simple graph
-- statement:
--   Every drawable finite simple graph on at least three vertices has at most 3|V|−6 edges. This supplies the target’s upper bound; a proof route is Euler’s formula and the face-edge incidence bound, with disconnected drawings handled explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_card_upper_bound__p2m_ad845c85_bbc7_45e1_b337_b2f3a4b80492_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      K.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
