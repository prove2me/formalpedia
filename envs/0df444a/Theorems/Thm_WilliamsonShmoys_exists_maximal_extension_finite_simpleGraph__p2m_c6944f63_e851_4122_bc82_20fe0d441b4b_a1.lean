-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_finite_simpleGraph__p2m_c6944f63_e851_4122_bc82_20fe0d441b4b_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_finite_simpleGraph__p2m_c6944f63_e851_4122_bc82_20fe0d441b4b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:45:04.82396+00:00
-- url     : https://prove2.me/theorems/96e34d65-5656-4c19-be9b-6b9447918a28
-- title:
--   Finite maximal extension principle for simple graphs
-- statement:
--   For any property of simple graphs on a finite vertex type, every graph satisfying the property has a property-satisfying supergraph that is maximal among property-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_finite_simpleGraph__p2m_c6944f63_e851_4122_bc82_20fe0d441b4b_a1 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hP : P G) : ∃ M : SimpleGraph V, G ≤ M ∧ P M ∧ ∀ H : SimpleGraph V, M ≤ H → P H → H = M := by sorry
