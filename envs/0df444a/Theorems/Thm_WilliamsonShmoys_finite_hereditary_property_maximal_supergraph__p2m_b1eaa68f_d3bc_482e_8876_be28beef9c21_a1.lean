-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_hereditary_property_maximal_supergraph__p2m_b1eaa68f_d3bc_482e_8876_be28beef9c21_a1
-- name    : WilliamsonShmoys.finite_hereditary_property_maximal_supergraph__p2m_b1eaa68f_d3bc_482e_8876_be28beef9c21_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T01:03:25.129711+00:00
-- url     : https://prove2.me/theorems/c8cf4474-432e-4dbd-85fe-0e5b17a700a6
-- title:
--   Finite maximal supergraph for a hereditary property
-- statement:
--   For any property of finite simple graphs that is preserved when edges are deleted, every graph satisfying the property has a supergraph that is maximal among graphs satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_hereditary_property_maximal_supergraph__p2m_b1eaa68f_d3bc_482e_8876_be28beef9c21_a1 {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop) (hhered : ∀ A B : SimpleGraph V, A ≤ B → P B → P A) (G : SimpleGraph V) (hG : P G) : ∃ T : SimpleGraph V, G ≤ T ∧ P T ∧ ∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T := by sorry
