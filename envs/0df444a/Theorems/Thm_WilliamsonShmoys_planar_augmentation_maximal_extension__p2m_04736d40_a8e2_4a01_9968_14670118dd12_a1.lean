-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_maximal_extension__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- name    : WilliamsonShmoys.planar_augmentation_maximal_extension__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:55:13.473462+00:00
-- url     : https://prove2.me/theorems/46949da2-af3a-4e18-8d79-5f0f20b92f74
-- title:
--   Extend a planar graph to an edge-maximal planar graph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that has no strictly larger planar supergraph on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_augmentation_maximal_extension__p2m_04736d40_a8e2_4a01_9968_14670118dd12_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
