-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_graph_extension__p2m_0be9f664_4886_4746_8cb3_c25ee67fb6aa_a1
-- name    : WilliamsonShmoys.finite_maximal_graph_extension__p2m_0be9f664_4886_4746_8cb3_c25ee67fb6aa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:04.716809+00:00
-- url     : https://prove2.me/theorems/e6afc572-07c7-4554-a881-52726379da51
-- title:
--   Finite maximal supergraph for any graph property
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.finite_maximal_graph_extension__p2m_0be9f664_4886_4746_8cb3_c25ee67fb6aa_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P M) :
    ∃ K : SimpleGraph V, M ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
