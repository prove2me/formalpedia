-- Prove2me | Theorems.Thm_finite_graph_predicate_maximal_extension__p2m_5e22ecc2_fcd1_4580_86fc_2603fce53c32_a1
-- name    : finite_graph_predicate_maximal_extension__p2m_5e22ecc2_fcd1_4580_86fc_2603fce53c32_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:49:15.072973+00:00
-- url     : https://prove2.me/theorems/92341989-ef4f-4865-9c43-c0970dd708d4
-- title:
--   Maximal predicate extension on a finite vertex type
-- statement:
--   For a finite vertex type, any graph `K` satisfying `P` has a `P`-satisfying supergraph maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_graph_predicate_maximal_extension__p2m_5e22ecc2_fcd1_4580_86fc_2603fce53c32_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hK : P K) :
    ∃ G : SimpleGraph V, K ≤ G ∧ P G ∧
      ∀ H : SimpleGraph V, G ≤ H → P H → H ≤ G := by
  sorry
