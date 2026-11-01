-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:35.099907+00:00
-- url     : https://prove2.me/theorems/547212f2-226f-4204-bd36-2967ffdb540d
-- title:
--   Connected planar supergraph augmentation
-- statement:
--   A finite graph with the given crossing-free drawing and at least three vertices has a connected graph on the same vertices that preserves the drawing property and contains at least as many edges. Add edges between components through the complementary regions of the drawing; the proof must formalize this construction for the explicit arc predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_e8818a47_c6bb_451e_9488_1f3faaa47e8f_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
      ∃ H : SimpleGraph V,
        HasPlanarDrawingOn H ∧ H.Connected ∧
          K.edgeFinset.card ≤
            (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
              H.edgeFinset.card)) := by
  sorry
