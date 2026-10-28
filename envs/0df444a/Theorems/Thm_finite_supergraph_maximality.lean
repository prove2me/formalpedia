-- Prove2me | Theorems.Thm_finite_supergraph_maximality
-- name    : finite_supergraph_maximality
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:16:39.525578+00:00
-- url     : https://prove2.me/theorems/2a5b6943-73ae-4d6d-9760-700727c65caa
-- title:
--   Finite maximal supergraph for any graph property
-- statement:
--   For any property of graphs on a finite vertex type, if one graph satisfies the property, there is a supergraph satisfying it that has no strictly larger supergraph satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_supergraph_maximality
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop) (hG : P G) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧ P H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) → P K → K = H := by sorry
