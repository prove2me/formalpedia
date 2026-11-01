-- Prove2me | Theorems.Thm_finite_maximal_subgraph_extension__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
-- name    : finite_maximal_subgraph_extension__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:33:47.825988+00:00
-- url     : https://prove2.me/theorems/d482e5fe-0b0f-483a-bdce-d1927a03a864
-- title:
--   Maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, any graph satisfying a downward-closed property has an extension satisfying the same property that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_subgraph_extension__p2m_8d3bb3a6_84b9_4586_bfa0_16ea8c3cae04_a1
    {V : Type} [Fintype V]
    (U : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hU : P U)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ W : SimpleGraph V, U ≤ W ∧ P W ∧
      ∀ N : SimpleGraph V, W ≤ N → P N → N ≤ W := by sorry
