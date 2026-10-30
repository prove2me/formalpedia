-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_supergraph_card_maximal__p2m_67fa8ed9_e0b5_4d6e_a654_f64162c7a789_a1
-- name    : WilliamsonShmoys.finite_supergraph_card_maximal__p2m_67fa8ed9_e0b5_4d6e_a654_f64162c7a789_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:11:21.484451+00:00
-- url     : https://prove2.me/theorems/dde616ab-b158-4cdb-9fc8-434d95427b83
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, if H has the property, then H has a supergraph K with the property whose edge count is at least H's and is at least the edge count of every further supergraph that also has the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_supergraph_card_maximal__p2m_67fa8ed9_e0b5_4d6e_a654_f64162c7a789_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
       letI : DecidableRel K.Adj := Classical.decRel K.Adj;
       H.edgeFinset.card ≤ K.edgeFinset.card) ∧
      (∀ L : SimpleGraph V, K ≤ L → P L →
        (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
         letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         L.edgeFinset.card ≤ K.edgeFinset.card)) := by sorry
