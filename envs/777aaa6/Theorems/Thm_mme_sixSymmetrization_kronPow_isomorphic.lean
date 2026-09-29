-- Prove2me | Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic
-- name    : mme_sixSymmetrization_kronPow_isomorphic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:02:04.818064+00:00
-- url     : https://prove2.me/theorems/c6639fc9-2555-446b-b9d7-bab86638964b
-- title:
--   DWZ six-symmetrization commutes with finite Kronecker powers
-- statement:
--   Let $T$ be an order-three tensor over a field, and let $\operatorname{Sym}_6(T)$ denote the full Duan--Wu--Zhou symmetrization: the product of the three cyclic mode rotations of $T$ and the first-two-mode swap of that cyclic product. For every natural number $n$, there is a tensor isomorphism
--
--   $$
--   \operatorname{Sym}_6(T)^{\otimes n} \cong \operatorname{Sym}_6(T^{\otimes n}).
--   $$
--
--   This finite structural identity permits a one-orientation restriction of $T^{\otimes n}$ to be symmetrized after the restriction, while matching the powered six-symmetric source used in Equation (25).
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.3, arXiv:2210.10173v5.

import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic

open MME

universe u

set_option autoImplicit false

theorem mme_sixSymmetrization_kronPow_isomorphic
    {K : Type u} [Field K]
    (T : TensorObj K 3) (n : ℕ) :
    TensorObj.Isomorphic
      ((sixSymmetrization T).kronPow n)
      (sixSymmetrization (T.kronPow n)) := by
  sorry
