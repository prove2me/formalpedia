-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_core_decomposition__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
-- name    : WilliamsonShmoys.planar_core_decomposition__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:06:29.867809+00:00
-- url     : https://prove2.me/theorems/81fa0627-b6f3-4235-872e-f4baa6a5f405
-- title:
--   Pruning a connected planar graph to its 2-core
-- statement:
--   Prune a connected planar graph by deleting vertices of degree at most one. Either its edge count is at most its vertex count, or a retained induced connected planar subgraph has at least three vertices, at least two neighbors per vertex, and the removed vertices account for at most one lost edge each.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_core_decomposition__p2m_5d9b8ff2_1349_4ea9_a2d4_f406c9d22c5b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    K.edgeSet.ncard <= Fintype.card V ∨
    ∃ S : Finset V,
      K.edgeSet.ncard <= (K.induce (↑S : Set V)).edgeSet.ncard + (Fintype.card V - S.card) ∧
      S.card <= Fintype.card V ∧
      3 <= S.card ∧
      (K.induce (↑S : Set V)).Connected ∧
      (∀ v : (↑S : Set V), 2 <= ((K.induce (↑S : Set V)).neighborSet v).ncard) ∧
      HasPlanarDrawingOn (K.induce (↑S : Set V)) := by sorry
