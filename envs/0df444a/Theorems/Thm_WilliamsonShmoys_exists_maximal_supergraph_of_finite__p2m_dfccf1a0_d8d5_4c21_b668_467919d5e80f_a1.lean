-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite__p2m_dfccf1a0_d8d5_4c21_b668_467919d5e80f_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_dfccf1a0_d8d5_4c21_b668_467919d5e80f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:52:45.685295+00:00
-- url     : https://prove2.me/theorems/aab44f74-6a8f-42f5-9fcd-78a6d0446912
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For a graph on a finite linearly ordered vertex type, any graph property satisfied by that graph has a supergraph satisfying the property that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite__p2m_dfccf1a0_d8d5_4c21_b668_467919d5e80f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      ∀ J : SimpleGraph V, H ≤ J → P J → H = J := by sorry
