-- Prove2me | Theorems.Thm_planar_supergraph_edge_lower_bound__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
-- name    : planar_supergraph_edge_lower_bound__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:11:35.184321+00:00
-- url     : https://prove2.me/theorems/6869bfe3-2b26-431f-90e7-27fe45b31a3f
-- title:
--   Planar graph has a drawable supergraph meeting the planar edge lower bound
-- statement:
--   Every drawable finite graph on at least three vertices has a drawable supergraph on the same vertex type with at least `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_supergraph_edge_lower_bound__p2m_dac4f87d_ced1_4d69_b072_bd58087807e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ HasPlanarDrawingOn M ∧
      LE.le (3 * Fintype.card V) (M.edgeSet.ncard + 6) := by
  sorry
