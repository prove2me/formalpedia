-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_profile_fine_factorization
-- name    : mme_stothers_phi233_exact_profile_fine_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:48:56.054347+00:00
-- url     : https://prove2.me/theorems/e1f34a3c-0ad4-4791-9d88-96ba11764dd3
-- title:
--   Exact phi_233 profiles factor into the ten literal fine-block powers
-- statement:
--   Fix a field $K$, a Coppersmith--Winograd parameter $q$, and an exact length-$2N$ profile of the ten ordered fine blocks in the $\varphi_{233}$ constituent. Let $m_r$ be the prescribed multiplicity of label $r$, namely the symmetric vector
--
--   $$
--   (m_0,\ldots,m_9)=(\alpha,\beta,\alpha,\gamma,\delta,\delta,\gamma,\alpha,\beta,\alpha).
--   $$
--
--   The ordered product of the ten algebraic component tensors, with component $r$ raised to the power $m_r$, restricts to the literal coordinatewise product of the fine source blocks selected by the profile.
--
--   This separates the tensor-algebraic payload of Lemma 5.1(v) from its hashing and entropy estimates: every selected exact profile has precisely the claimed ten component powers, with no replacement of the literal source by a fictitious direct sum.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, especially the ten fine constituents and the symmetric profile used in the type-2 analysis; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_exact_label
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_stothers_phi233_pattern_injective
import Theorems.Thm_mme_stothers_phi233_fine_component_restrictions
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_exact_profile_fine_factorization
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 10 (fun r ↦
        (MME.StothersFourth.Phi233.componentObj K q r).kronPow
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r)))
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j))) := by
  sorry
