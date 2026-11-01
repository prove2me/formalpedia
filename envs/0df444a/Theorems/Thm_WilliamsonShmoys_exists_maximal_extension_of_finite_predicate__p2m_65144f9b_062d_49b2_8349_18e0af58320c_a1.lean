-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_predicate__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:32:22.288547+00:00
-- url     : https://prove2.me/theorems/060318e6-9aa2-44ce-a8eb-f04f288fc5e7
-- title:
--   Maximal extension for a finite downward-closed graph property
-- statement:
--   For a finite ordered vertex type, every graph satisfying a downward-closed property has an extension satisfying that property which is maximal among such extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_finite_predicate__p2m_65144f9b_062d_49b2_8349_18e0af58320c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hL : P L)
    (hdown : ∀ {G H : SimpleGraph V}, G ≤ H → P H → P G) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ P T ∧
        ∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T := by sorry
