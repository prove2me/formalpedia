-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_completion_maximal_extension__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
-- name    : WilliamsonShmoys.maximal_planar_completion_maximal_extension__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:22:37.253229+00:00
-- url     : https://prove2.me/theorems/76ca258b-4f2e-4801-9d46-2c2421541685
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable graph that has no strictly larger drawable supergraph on the same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_completion_maximal_extension__p2m_bb1eb53b_a90c_47ce_9dd0_93bdb2c805fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X) :
    ∃ Y : SimpleGraph V, X ≤ Y ∧ HasPlanarDrawingOn Y ∧
      ∀ Z : SimpleGraph V, Y ≤ Z → HasPlanarDrawingOn Z → Z ≤ Y := by sorry
