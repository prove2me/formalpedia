-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_property_has_maximal_extension__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
-- name    : WilliamsonShmoys.finite_hereditary_property_has_maximal_extension__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:27:14.28659+00:00
-- url     : https://prove2.me/theorems/84dd79e9-e552-4829-8ce7-c4550dba5216
-- title:
--   Finite hereditary properties admit maximal extensions
-- statement:
--   For a finite vertex type, any property of graphs that is preserved when edges are removed has a maximal extension of every graph satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_hereditary_property_has_maximal_extension__p2m_918f6ef7_b742_4a7a_b6c7_f41fd05476c6_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K)
    (hmono : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
      ∀ M : SimpleGraph V, L ≤ M → P M → M = L := by sorry
