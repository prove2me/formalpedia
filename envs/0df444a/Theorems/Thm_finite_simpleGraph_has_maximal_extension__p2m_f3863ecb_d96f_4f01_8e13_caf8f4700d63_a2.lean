-- Prove2me | Theorems.Thm_finite_simpleGraph_has_maximal_extension__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
-- name    : finite_simpleGraph_has_maximal_extension__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:49.676381+00:00
-- url     : https://prove2.me/theorems/40238eb7-e613-4918-9b44-98364a27640b
-- title:
--   Finite downward-closed properties admit maximal extensions
-- statement:
--   For a finite vertex type, any graph satisfying a downward-closed property has an extension satisfying that property which is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_simpleGraph_has_maximal_extension__p2m_f3863ecb_d96f_4f01_8e13_caf8f4700d63_a2
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V)
    (hG : P G)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
