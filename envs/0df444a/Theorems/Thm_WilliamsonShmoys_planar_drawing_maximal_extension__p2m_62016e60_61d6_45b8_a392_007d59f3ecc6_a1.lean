-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:26:17.23964+00:00
-- url     : https://prove2.me/theorems/3043441f-698f-49eb-9867-9197561360be
-- title:
--   Maximal planar supergraph extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal under inclusion among drawable supergraphs. This isolates the finite edge-maximization step; a proof can maximize edge count among the finitely many supergraphs and use strict inclusion to increase that count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_62016e60_61d6_45b8_a392_007d59f3ecc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L →
          WilliamsonShmoys.HasPlanarDrawingOn L → L = K := by sorry
