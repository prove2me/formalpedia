-- Prove2me | Theorems.Thm_mme_sixSymmetrization_bigAdd_const_isomorphic
-- name    : mme_sixSymmetrization_bigAdd_const_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:06:44.077185+00:00
-- url     : https://prove2.me/theorems/9c5951f2-55e3-42d8-b618-b3111b2a37d6
-- title:
--   Six-symmetrization of identical direct-sum blocks
-- statement:
--   Let $T$ be an order-three tensor over a field. The full Duan--Wu--Zhou six-symmetrization of a direct sum of $k$ identical copies of $T$ is tensor-isomorphic to a direct sum of $k^6$ identical copies of the six-symmetrization of $T$:
--
--   $$
--   \operatorname{Sym}_6\!\left(\bigoplus_{i=1}^{k}T\right) \cong \bigoplus_{j=1}^{k^6}\operatorname{Sym}_6(T).
--   $$
--
--   This is the finite distributive identity that turns the number of repaired standard copies produced by asymmetric hashing into the sixth-power multiplicity required by the square analysis.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3 and Equation (25), arXiv:2210.10173v5.

import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_bigAdd_const_isomorphic
    {K : Type u} [Field K]
    (T : TensorObj K 3) (k : ℕ) :
    TensorObj.Isomorphic
      (sixSymmetrization
        (TensorObj.bigAdd (fun _ : Fin k => T)))
      (TensorObj.bigAdd
        (fun _ : Fin (k ^ (6 : ℕ)) => sixSymmetrization T)) := by
  sorry
