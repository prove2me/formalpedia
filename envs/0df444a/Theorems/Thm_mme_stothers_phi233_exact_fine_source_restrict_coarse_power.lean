-- Prove2me | Theorems.Thm_mme_stothers_phi233_exact_fine_source_restrict_coarse_power
-- name    : mme_stothers_phi233_exact_fine_source_restrict_coarse_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:03:02.788657+00:00
-- url     : https://prove2.me/theorems/d5a2bfde-e1bb-4ad9-9003-c27e7fdc2c82
-- title:
--   An exact phi_233 fine profile restricts from the literal coarse power
-- statement:
--   Fix a field $K$, a Coppersmith--Winograd parameter $q$, and a length-$2N$ exact profile of the ten fine blocks making up the fourth-power constituent $\varphi_{233}$. If $F_{r_j}$ is the literal ordered square-block pair selected at coordinate $j$, then
--
--   $$
--   \bigotimes_{j<2N} F_{r_j}\;\le\;\varphi_{233}^{\otimes 2N}.
--   $$
--
--   Thus the fine tensor product used by the type-2 entropy and hashing calculation is obtained by an actual modewise linear restriction of the corresponding power of the literal coarse constituent. This supplies the fine-to-coarse tensor bridge needed before isolating exact profiles.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5 and Lemma 5.1(v), printed pp. 365--366, especially the ten fine constituents of T_{233}; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_stothers_phi233_exact_label
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_exact_fine_source_restrict_coarse_power
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j)))
      ((MME.StothersFourth.cwFourthConstituent K q 2 3 3).kronPow
        (2 * N)) := by
  sorry
