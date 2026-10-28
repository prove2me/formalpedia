-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_finite_property_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- name    : WilliamsonShmoys.exists_maximal_supergraph_finite_property_9538c7a8_17aa_406f_ad1c_e0bdce92c761
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:55:07.945052+00:00
-- url     : https://prove2.me/theorems/079a27ea-1b59-4fdd-ac05-40f67e265b7a
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   For a finite vertex type, any graph satisfying a subgraph-hereditary property is contained in a supergraph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_finite_property_9538c7a8_17aa_406f_ad1c_e0bdce92c761
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G)
    (hmono : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      (∀ K : SimpleGraph V, H ≤ K → P K → K = H) := by sorry
