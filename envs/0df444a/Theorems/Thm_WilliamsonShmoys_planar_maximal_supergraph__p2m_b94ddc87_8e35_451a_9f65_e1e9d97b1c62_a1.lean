-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:36.6137+00:00
-- url     : https://prove2.me/theorems/1a00a7f7-bc24-43af-b949-dc9c9c992368
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every finite drawable simple graph is contained in an inclusion-maximal drawable simple graph on the same vertex set. The finite collection of simple graphs on V and the drawable witness for H give a maximal choice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_b94ddc87_8e35_451a_9f65_e1e9d97b1c62_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
