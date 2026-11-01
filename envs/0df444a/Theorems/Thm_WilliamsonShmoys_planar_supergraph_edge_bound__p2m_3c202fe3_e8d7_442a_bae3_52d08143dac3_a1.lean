-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_bound__p2m_3c202fe3_e8d7_442a_bae3_52d08143dac3_a1
-- name    : WilliamsonShmoys.planar_supergraph_edge_bound__p2m_3c202fe3_e8d7_442a_bae3_52d08143dac3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:39.017729+00:00
-- url     : https://prove2.me/theorems/37b1f122-e21a-4ccc-9539-0e6943b4c397
-- title:
--   Planar supergraph with the planar edge lower bound
-- statement:
--   Every drawable simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_edge_bound__p2m_3c202fe3_e8d7_442a_bae3_52d08143dac3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    exists T : SimpleGraph V,
      L <= T /\ HasPlanarDrawingOn T /\
        (letI : DecidableRel T.Adj := Classical.decRel T.Adj;
          3 * Fintype.card V <= T.edgeFinset.card + 6) := by sorry
