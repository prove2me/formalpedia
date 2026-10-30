-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_b48f5d89_dd8c_44de_b172_78fd0037e2dc_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_b48f5d89_dd8c_44de_b172_78fd0037e2dc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:42.980197+00:00
-- url     : https://prove2.me/theorems/87473913-4998-4925-9ca5-b37691d71c03
-- title:
--   Finite maximal supergraph for a graph predicate
-- statement:
--   For any predicate on graphs over a finite linearly ordered vertex type, a connected graph satisfying the predicate has a connected supergraph satisfying it that is maximal under supergraph inclusion and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_b48f5d89_dd8c_44de_b172_78fd0037e2dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (P : SimpleGraph V → Prop)
    (hP : P K)
    (hconn : K.Connected) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       K ≤ H ∧ H.Connected ∧ P H ∧
       (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
         (letI : DecidableRel L.Adj := dL
          H ≤ L → P L → L ≤ H)) ∧
       K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
