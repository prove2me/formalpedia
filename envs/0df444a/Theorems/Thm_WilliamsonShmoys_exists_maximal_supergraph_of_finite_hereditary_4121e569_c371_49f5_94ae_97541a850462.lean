-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_hereditary_4121e569_c371_49f5_94ae_97541a850462
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_hereditary_4121e569_c371_49f5_94ae_97541a850462
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:23:44.319552+00:00
-- url     : https://prove2.me/theorems/42fa631f-18a0-4925-a9d0-4688468d1584
-- title:
--   Maximal supergraph for a hereditary graph property on a finite vertex type
-- statement:
--   On a finite vertex type, any graph satisfying an edge-hereditary property is contained in a supergraph that is maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_hereditary_4121e569_c371_49f5_94ae_97541a850462
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧
        ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
