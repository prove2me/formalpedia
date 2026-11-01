-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_extension_of_predicate__p2m_69d74bef_9aa8_40b9_8469_f44173b0c825_a1
-- name    : WilliamsonShmoys.maximal_extension_of_predicate__p2m_69d74bef_9aa8_40b9_8469_f44173b0c825_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:49.59348+00:00
-- url     : https://prove2.me/theorems/4393cf6f-c289-4339-9d1f-7ded4179c9b0
-- title:
--   Maximal extension for a predicate on finite graphs
-- statement:
--   For any predicate on simple graphs over a finite ordered vertex type, every graph satisfying the predicate is contained in a predicate-satisfying graph that is maximal among its predicate-satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_extension_of_predicate__p2m_69d74bef_9aa8_40b9_8469_f44173b0c825_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (K : SimpleGraph V) (hK : P K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ P L ∧
        ∀ M : SimpleGraph V, P M → L ≤ M → M = L := by
  sorry
