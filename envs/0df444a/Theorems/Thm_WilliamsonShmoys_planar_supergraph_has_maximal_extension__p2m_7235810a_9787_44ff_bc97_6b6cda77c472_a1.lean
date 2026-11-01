-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_has_maximal_extension__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- name    : WilliamsonShmoys.planar_supergraph_has_maximal_extension__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:55:35.852636+00:00
-- url     : https://prove2.me/theorems/db589962-0581-431b-85a4-f73500e19284
-- title:
--   Finite maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on that same type that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_has_maximal_extension__p2m_7235810a_9787_44ff_bc97_6b6cda77c472_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : HasPlanarDrawingOn U) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      ∀ X : SimpleGraph V, W ≤ X → HasPlanarDrawingOn X → X ≤ W := by sorry
