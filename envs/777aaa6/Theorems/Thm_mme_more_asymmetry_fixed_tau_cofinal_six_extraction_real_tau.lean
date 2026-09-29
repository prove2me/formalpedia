-- Prove2me | Theorems.Thm_mme_more_asymmetry_fixed_tau_cofinal_six_extraction_real_tau
-- name    : mme_more_asymmetry_fixed_tau_cofinal_six_extraction_real_tau
-- status  : Open
-- author  : @WillR
-- created : 2026-09-07T07:51:35.674717+00:00
-- url     : https://prove2.me/theorems/e5acea12-c15b-43b8-9abb-57195c8af2f5
-- title:
--   More Asymmetry: cofinal six-symmetric finite extraction at real tau
-- statement:
--   For every field (K), the complete-split, recursive, and hole-repair construction for the released (CW_5^{otimes4}) witness supplies an explicit asymptotic extraction for the six-symmetrized tensor.  More precisely, there is a real (V>2401), a cofinal sequence of powers (s(n)	oinfty), and errors (e_n	o0) such that, for all sufficiently large (n), the power
--
--   $$
--   \operatorname{sym}_6(CW_5^{\otimes4})^{\otimes s(n)}
--   $$
--
--   restricts to a finite direct sum of genuine matrix-multiplication tensors whose (	au)-weighted volume is at least
--
--   $$
--   (V^6)^{s(n)}(1-e_n),\qquad \tau=3952233/5000000.
--   $$
--
--   This is the explicit finite-extraction form of the source's value-surplus step.  The child retains the actual tensor restrictions, the cofinal power sequence, and the vanishing relative error; it does not assume an optimizer certificate or a scalar surrogate.  Once proved, the standard cofinal-extraction theorem turns this witness into `HasSixSymmetricTauValueAtLeast` for the mission's frontier theorem.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, SODA 2025, arXiv:2404.16349v2, Theorems 5.3, 6.2, 6.4 and Section 7, pp. 18--20 and 40--41; https://arxiv.org/abs/2404.16349v2; released archive/data hashes recorded on the live mission.  The statement expands the platform's six-symmetrized tau-value witness into its cofinal finite-extraction form.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_fixed_tau_cofinal_six_extraction_real_tau
    {K : Type u} [Field K] :
    ∃ V : ℝ, (2401 : ℝ) < V ∧
      ∃ (s : ℕ → ℕ) (error : ℕ → ℝ),
        Tendsto s atTop atTop ∧
        Tendsto error atTop (nhds 0) ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ (k : ℕ) (a b c : Fin k → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
              ((sixSymmetrization
                (MME.StothersFourth.cwFourthObj K 5)).kronPow (s n)) ∧
              (V ^ (6 : ℕ)) ^ (s n) * (1 - error n) ≤
              ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^
                ((3952233 : ℝ) / 5000000)) := by sorry
