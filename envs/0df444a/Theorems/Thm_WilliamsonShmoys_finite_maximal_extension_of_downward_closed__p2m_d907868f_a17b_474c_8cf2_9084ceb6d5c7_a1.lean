-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_extension_of_downward_closed__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
-- name    : WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:13:57.013566+00:00
-- url     : https://prove2.me/theorems/4d4be376-d3bf-4589-a3ff-b9898464a22d
-- title:
--   Maximal extension for a downward-closed graph predicate
-- statement:
--   For a finite vertex type, any graph satisfying a downward-closed predicate has an extension that is maximal among graphs satisfying that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_maximal_extension_of_downward_closed__p2m_d907868f_a17b_474c_8cf2_9084ceb6d5c7_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G)
    (C : SimpleGraph V) (hC : P C) :
    ∃ H : SimpleGraph V, C ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by
  sorry
