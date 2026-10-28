-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_extension_of_finite_downward_closed_property
-- name    : WilliamsonShmoys.exists_maximal_extension_of_finite_downward_closed_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:51:03.120834+00:00
-- url     : https://prove2.me/theorems/231e235f-6901-480f-a220-3fbc765852d9
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   On a finite vertex type, any graph satisfying a downward-closed property has a supergraph satisfying that property which is maximal among such supergraphs. Process the finite set of possible edges and retain each addition when the property remains true; downward closure then rules out every property-preserving strict supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_extension_of_finite_downward_closed_property
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K)
    (hdown : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G) :
    ∃ T : SimpleGraph V, K ≤ T ∧ P T ∧
      ∀ U : SimpleGraph V, T ≤ U → P U → U = T := by sorry
