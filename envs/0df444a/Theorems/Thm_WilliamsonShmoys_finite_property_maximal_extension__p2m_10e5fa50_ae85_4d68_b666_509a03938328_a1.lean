-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_property_maximal_extension__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1
-- name    : WilliamsonShmoys.finite_property_maximal_extension__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:26:49.233212+00:00
-- url     : https://prove2.me/theorems/6fac8935-626c-453a-b732-3699a8acdf35
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   For any hereditary property of simple graphs on a finite vertex type, every graph with the property is contained in an inclusion-maximal graph with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_property_maximal_extension__p2m_10e5fa50_ae85_4d68_b666_509a03938328_a1 {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) (hsub : ∀ ⦃A B : SimpleGraph V⦄, P B → A ≤ B → P A) : ∃ T : SimpleGraph V, P T ∧ G ≤ T ∧ ∀ K : SimpleGraph V, P K → T ≤ K → K ≤ T := by sorry
