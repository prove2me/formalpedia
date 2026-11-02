-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- name    : WilliamsonShmoys.maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:21:37.49844+00:00
-- url     : https://prove2.me/theorems/934089cc-df1f-4da4-b973-c115b2e35af8
-- title:
--   Maximal planar augmentation on a fixed vertex type
-- statement:
--   Given a finite drawn planar graph on at least three vertices, there is a planar supergraph on the same vertex type that is maximal among planar supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_augmentation__p2m_b05b2ac9_cf86_42cd_81eb_d15df4254060_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by sorry
