-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:27:18.855217+00:00
-- url     : https://prove2.me/theorems/cebdf6a5-ed21-4e3f-9527-133aad01d215
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite planar graph has a planar supergraph on the same vertex set that is maximal under inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_2c3c6158_456c_482b_9c8f_03d7360d8952_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
