-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_downward_closed__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
-- name    : WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:48:21.215016+00:00
-- url     : https://prove2.me/theorems/10545618-b4b5-4074-9cf5-b3ff4c8d7112
-- title:
--   Finite downward-closed graph properties have maximal extensions
-- statement:
--   For a finite vertex type, any graph satisfying a downward-closed property is contained in a supergraph satisfying that property that has no strictly larger supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_downward_closed__p2m_138d462c_20bd_43cc_9c59_565c454fd505_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {H K : SimpleGraph V}, H ≤ K → P K → P H)
    (G : SimpleGraph V) (hG : P G) :
    ∃ Q : SimpleGraph V,
      G ≤ Q ∧ P Q ∧
        ∀ R : SimpleGraph V, Q ≤ R → P R → R ≤ Q := by
  sorry
