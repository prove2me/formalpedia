-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_cea2ff1b_6ac8_4e7a_9f09_37a536780796_a2
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_cea2ff1b_6ac8_4e7a_9f09_37a536780796_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:37:51.211676+00:00
-- url     : https://prove2.me/theorems/82664a01-269d-42c1-bb16-28d149415c02
-- title:
--   Every drawable graph has a drawable supergraph meeting the planar edge bound
-- statement:
--   For a finite drawable simple graph on at least three vertices, there is a drawable supergraph on the same vertex set with at least 3n−6 edges. This removes the target’s maximality premise by supplying the required supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_cea2ff1b_6ac8_4e7a_9f09_37a536780796_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      R ≤ T ∧
      3 * Fintype.card V ≤ T.edgeSet.ncard + 6 := by sorry
