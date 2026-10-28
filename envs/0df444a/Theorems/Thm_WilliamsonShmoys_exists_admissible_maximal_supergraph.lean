-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_admissible_maximal_supergraph
-- name    : WilliamsonShmoys.exists_admissible_maximal_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:51:16.285346+00:00
-- url     : https://prove2.me/theorems/306da203-94b6-4fe8-bdfa-eee70be0b42c
-- title:
--   Finite maximal admissible supergraph
-- statement:
--   For any property on graphs over a finite vertex type, if H satisfies the property, then H has a supergraph satisfying the property that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_admissible_maximal_supergraph
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  sorry
