-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_property_has_maximal_supergraph__p2m_e39dc392_ef53_43de_92b9_a9ba96581299_a2
-- name    : WilliamsonShmoys.finite_property_has_maximal_supergraph__p2m_e39dc392_ef53_43de_92b9_a9ba96581299_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:24:20.664132+00:00
-- url     : https://prove2.me/theorems/c52a4620-4d33-428e-9d7e-f54fc16c4c0f
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a graph on a finite vertex type, any downward-closed graph property that holds of the graph has a supergraph maximal under edge inclusion among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_property_has_maximal_supergraph__p2m_e39dc392_ef53_43de_92b9_a9ba96581299_a2
    {V : Type} [Fintype V]
    (N : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hdown : ∀ ⦃A B : SimpleGraph V⦄, A ≤ B → P B → P A)
    (hN : P N) :
    ∃ K : SimpleGraph V,
      N ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by sorry
