-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_supergraph__p2m_dc3c3c5f_ee3d_4118_9c6e_a3edf0d67e38_a1
-- name    : WilliamsonShmoys.finite_maximal_supergraph__p2m_dc3c3c5f_ee3d_4118_9c6e_a3edf0d67e38_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:16:12.544625+00:00
-- url     : https://prove2.me/theorems/07bfba04-2c8b-41b3-8207-e09f21c76255
-- title:
--   Finite maximal supergraph for any nonempty graph property
-- statement:
--   For any property of simple graphs on a finite vertex type, if at least one graph has the property, there is a property-satisfying supergraph that is maximal under inclusion among property-satisfying graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_supergraph__p2m_dc3c3c5f_ee3d_4118_9c6e_a3edf0d67e38_a1
    {V : Type} [Fintype V] (P : SimpleGraph V → Prop)
    (Z : SimpleGraph V) (hZ : P Z) :
    ∃ W : SimpleGraph V, Z ≤ W ∧ P W ∧
      ∀ X : SimpleGraph V, W ≤ X → P X → X ≤ W := by
  sorry
