-- Prove2me | Theorems.Thm_mme_more_asymmetry_six_symmetric_tau_value_surplus
-- name    : mme_more_asymmetry_six_symmetric_tau_value_surplus
-- status  : Open
-- author  : @WillR
-- created : 2026-09-11T20:16:27.31241+00:00
-- url     : https://prove2.me/theorems/4941edfd-6de9-445b-abcb-1c5925a9cf08
-- title:
--   More Asymmetry: six-symmetric tau-value surplus
-- statement:
--   For every field K, put T=CW_5^{\otimes4} and
--   tau=3952233/5000000.  The source-faithful global, recursive, and
--   hole-repair construction for the released More Asymmetry witness yields a
--   real V>2401 for which the six-symmetrized tensor has tau-value at least V.
--   This scalar child deliberately isolates the numerical/value-surplus interface;
--   the parent frontier expands the same assertion into actual cofinal finite
--   restrictions, power indices, and vanishing relative error.  No floating-point
--   certificate or scalar surrogate is used as a premise.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, SODA 2025, arXiv:2404.16349v2, Theorems 5.3, 6.2, 6.4 and Section 7, pp. 18--20 and 40--41; https://arxiv.org/abs/2404.16349v2; released archive/data hashes recorded on the live mission.  This is the scalar value-surplus interface for the source's actual six-symmetrized fourth-CW tensor.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_six_symmetric_tau_value_surplus
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      HasSixSymmetricTauValueAtLeast
        (MME.StothersFourth.cwFourthObj K 5)
        ((3952233 : ℝ) / 5000000) V := by sorry
