-- Prove2me | Theorems.Thm_mme_stothers_theorem53_positive_profile_form
-- name    : mme_stothers_theorem53_positive_profile_form
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-21T23:34:26.648906+00:00
-- url     : https://prove2.me/theorems/75b58d28-1c39-4e7d-bf24-9cd0ab7fe74e
-- title:
--   Theorem 5.3 from a positive admissible profile alone
-- statement:
--   Let $K$ be a field, let $2\le3\tau\le3$, and let $a\in Z$ be a strictly positive fourth-power profile. Write $\mathcal E(c)=\prod_i c_i^{n_i c_i}$, and let $G(6,\tau,a)$ denote the platform's uncorrected global fourth-power rate $\mathrm{globalRate}(6,\tau,a,a)$.
--
--   There exists a strictly positive stationary profile $b\in\mathcal N$ with $a-b\in Y$ such that, for every real $V$ satisfying
--
--   $$0\le V<G(6,\tau,a)\,\frac{\mathcal E(b)}{\mathcal E(a)},$$
--
--   the literal fourth power $CW_6^{\otimes4}$ has $\tau$-value at least $V$.
--
--   This removes the need to supply a stationary profile or an attained entropy minimizer as a hypothesis when applying the corrected same-marginal value bound. The entropy correction uses the minimizing profile on the slice through $a$.
-- source:
--   Derived positive-profile form of A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Roy. Soc. Edinburgh A 143 (2013), printed p. 358, Equation (3.4), and pp. 367-368, Equation (5.2), Lemma 5.2 and Theorem 5.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. Uses the corrected entropy-ratio orientation already formalized in the platform stationary form, together with existence of the positive stationary representative.

import Definitions.Def_mme_stothers_fourth_data
open MME
universe u
set_option autoImplicit false

theorem mme_stothers_theorem53_positive_profile_form
    {K : Type u} [Field K]
    (tau : ℝ) (htauLower : 2 ≤ 3 * tau) (htauUpper : 3 * tau ≤ 3)
    (a : Fin 10 → ℝ) (ha : MME.StothersFourth.InZ a)
    (hapos : ∀ i, 0 < a i) :
    ∃ b : Fin 10 → ℝ, MME.StothersFourth.InN b ∧ (∀ i, 0 < b i) ∧
      MME.StothersFourth.InY (fun i ↦ a i - b i) ∧
      ∀ V : ℝ, 0 ≤ V →
        V < MME.StothersFourth.globalRate 6 tau a a *
          (MME.StothersFourth.entropyProduct b / MME.StothersFourth.entropyProduct a) →
        HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by sorry
