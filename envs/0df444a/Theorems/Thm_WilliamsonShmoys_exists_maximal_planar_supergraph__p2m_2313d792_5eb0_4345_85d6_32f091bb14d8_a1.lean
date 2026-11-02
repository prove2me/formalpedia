-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:43:54.5862+00:00
-- url     : https://prove2.me/theorems/1910be3b-5d3c-446e-bde3-91f415447a3b
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2313d792_5eb0_4345_85d6_32f091bb14d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K := by sorry
