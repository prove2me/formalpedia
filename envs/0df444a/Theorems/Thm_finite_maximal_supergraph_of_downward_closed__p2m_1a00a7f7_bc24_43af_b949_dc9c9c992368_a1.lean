-- Prove2me | Theorems.Thm_finite_maximal_supergraph_of_downward_closed__p2m_1a00a7f7_bc24_43af_b949_dc9c9c992368_a1
-- name    : finite_maximal_supergraph_of_downward_closed__p2m_1a00a7f7_bc24_43af_b949_dc9c9c992368_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:27:15.465552+00:00
-- url     : https://prove2.me/theorems/c7432618-08fc-4a77-9546-40c80146e77b
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, any graph satisfying a property that is preserved when edges are removed has a supergraph maximal among graphs satisfying that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_maximal_supergraph_of_downward_closed__p2m_1a00a7f7_bc24_43af_b949_dc9c9c992368_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hdown : ∀ {G G' : SimpleGraph V}, G ≤ G' → P G' → P G) :
    ∃ K : SimpleGraph V, H ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  sorry
