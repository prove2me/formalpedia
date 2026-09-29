-- Prove2me | Theorems.Thm_mme_sixSymmetrization_kronFin_isomorphic
-- name    : mme_sixSymmetrization_kronFin_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:34:43.649769+00:00
-- url     : https://prove2.me/theorems/a49d8f6a-1d45-4585-8305-de3e4834ecb2
-- title:
--   Six-symmetrization commutes with finite heterogeneous products
-- statement:
--   For any finite family of order-three tensors $T_1,\ldots,T_n$ over a field, full Duan--Wu--Zhou six-symmetrization commutes with their heterogeneous Kronecker product, up to tensor isomorphism:
--
--   $$
--   \bigotimes_{i=1}^{n}\operatorname{Sym}_6(T_i) \cong \operatorname{Sym}_6\!\left(\bigotimes_{i=1}^{n}T_i\right).
--   $$
--
--   This identity permits the fifteen Table-2 component extractions to be proved separately and then assembled into the six-symmetrization of the literal standard tensor.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3 and the component product in Equation (25), arXiv:2210.10173v5.

import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_toQ_kronFin

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i ↦ sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  sorry
