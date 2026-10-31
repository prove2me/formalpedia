-- Prove2me | Theorems.Thm_finiteHereditaryMaximalSupergraph__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
-- name    : finiteHereditaryMaximalSupergraph__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:37:08.378493+00:00
-- url     : https://prove2.me/theorems/f33abbf4-96d9-4363-8418-29cc7e5ff2c9
-- title:
--   Finite maximal supergraph for a downward-closed property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property has a supergraph satisfying that property which has no strictly larger supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finiteHereditaryMaximalSupergraph__p2m_3647f07c_750e_4c3e_8be8_ca29b1e4d823_a1
    {V : Type} [Fintype V] [DecidableEq V] (P : SimpleGraph V → Prop)
    (hmono : ∀ ⦃G J : SimpleGraph V⦄, G ≤ J → P J → P G)
    (K : SimpleGraph V) (hK : P K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧
      (∀ J : SimpleGraph V, H ≤ J → P J → J ≤ H) := by
  sorry
