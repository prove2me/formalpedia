-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:56:45.959346+00:00
-- url     : https://prove2.me/theorems/68e22fb0-4b87-435a-8af6-90e66d0b97bb
-- title:
--   Finite maximal extension for an arbitrary graph predicate
-- statement:
--   For a finite vertex type, any graph satisfying a predicate has a supergraph satisfying that predicate which is maximal under graph inclusion. No monotonicity assumption on the predicate is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_finite_choice__p2m_168460db_bad2_471e_a83e_74dae3ce8af4_a2
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hT : P T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ P U ∧
        ∀ W : SimpleGraph V, U ≤ W → P W → W = U := by sorry
