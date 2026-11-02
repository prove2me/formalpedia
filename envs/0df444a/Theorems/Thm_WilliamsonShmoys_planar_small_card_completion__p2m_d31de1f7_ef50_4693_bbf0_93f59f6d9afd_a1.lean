-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_small_card_completion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- name    : WilliamsonShmoys_planar_small_card_completion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:26.769535+00:00
-- url     : https://prove2.me/theorems/6ce4ca43-3f24-470a-9f5f-602e4f1a05ae
-- title:
--   Complete planar graph completion for fewer than three vertices
-- statement:
--   On a finite linearly ordered vertex type with fewer than three vertices, complete any drawable simple graph to the complete graph; it remains drawable and has the stated binomial edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_small_card_completion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hsmall : Fintype.card V < 3) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H ≤ K ∧
      K.edgeFinset.card = (Fintype.card V).choose 2 := by sorry
