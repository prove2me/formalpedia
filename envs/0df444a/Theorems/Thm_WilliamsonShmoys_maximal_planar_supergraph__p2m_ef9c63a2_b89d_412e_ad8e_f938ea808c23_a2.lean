-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:10:29.815274+00:00
-- url     : https://prove2.me/theorems/94e2ffb3-1367-478b-9978-8ad68033036a
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph maximal under inclusion among drawable graphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_ef9c63a2_b89d_412e_ad8e_f938ea808c23_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
