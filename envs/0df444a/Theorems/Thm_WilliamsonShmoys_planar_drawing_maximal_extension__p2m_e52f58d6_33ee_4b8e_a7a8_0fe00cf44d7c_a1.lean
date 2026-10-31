-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:11.345379+00:00
-- url     : https://prove2.me/theorems/b48f5d89-dd8c-44de-b172-78fd0037e2dc
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every connected graph with a planar drawing on a finite vertex set is contained in a connected planar graph on that same vertex set that is maximal under planar supergraph inclusion. The extension preserves the drawing property, and its edge count is at least the original edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_e52f58d6_33ee_4b8e_a7a8_0fe00cf44d7c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel H.Adj := dH
       K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       (∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
         (letI : DecidableRel L.Adj := dL
          H ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ H)) ∧
       K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
