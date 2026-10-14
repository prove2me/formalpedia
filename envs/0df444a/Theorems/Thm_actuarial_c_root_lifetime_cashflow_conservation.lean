-- Prove2me | Theorems.Thm_actuarial_c_root_lifetime_cashflow_conservation
-- name    : actuarial_c_root_lifetime_cashflow_conservation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-13T06:23:48.465639+00:00
-- url     : https://prove2.me/theorems/f7f0b2c3-1131-4e99-9a02-826626be073d
-- title:
--   Life-assurance cashflows: mortality-law valuation, claims moments, premium balance and annuity identities
-- statement:
--   From one normalised finite mortality law and one discount basis, reconcile actual year-end death claims with death-mass sums, actual survivor payments with maturity probabilities, and the mutually exclusive endowment components. Independently establish finite insurance–annuity conservation and claim/endowment second moments. Extend the same valuation to a deferred period, delayed settlement and increasing death benefits. When the premium-annuity denominator is positive, establish zero expected loss at the net premium. Finally, reconcile the event-derived level assurance with the published commutation sum.
--
--   Mathematical relations:
--
--   $$
--   A_n^1+v^n S(n)+(1-v)\ddot a_n=1,
--   \qquad
--   \mathbb E[Z^2]=\sum_{j=0}^{h-1}v^{2(j+1)}b_j^2p_j.
--   $$
--
--   The zero-term and censoring boundaries remain explicit, and the net-premium identity is conditional on a strictly positive denominator. The declaration proves none of these claims yet; all are genuine open proof obligations.
-- source:
--   Original derived finite life-contingency specification; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd edition, Chapter 5, Section 5.7, endowment and annuity identity, printed p. 71. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. The cited material establishes actuarial context and payment conventions. This particular finite Lean declaration is not a verbatim published theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_total
import Definitions.Def_actuarial_c_surv
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_massPV
import Definitions.Def_actuarial_c_termPath
import Definitions.Def_actuarial_c_term
import Definitions.Def_actuarial_c_purePath
import Definitions.Def_actuarial_c_pure
import Definitions.Def_actuarial_c_pureMass
import Definitions.Def_actuarial_c_endowPath
import Definitions.Def_actuarial_c_endow
import Definitions.Def_actuarial_c_due
import Definitions.Def_actuarial_c_second
import Definitions.Def_actuarial_c_secondMass
import Definitions.Def_actuarial_c_weightedDue
import Definitions.Def_actuarial_c_differenceBenefit
import Definitions.Def_actuarial_c_termSecond
import Definitions.Def_actuarial_c_endowSecond
import Definitions.Def_actuarial_c_massCohort
import Definitions.Def_actuarial_faM

import Definitions.Def_actuarial_c_deferred
import Definitions.Def_actuarial_c_delayEPV
import Definitions.Def_actuarial_c_expectedLoss
import Definitions.Def_actuarial_c_inc
import Definitions.Def_actuarial_c_increasingDue
import Definitions.Def_actuarial_c_netPremium

open ActuarialAssurances

theorem actuarial_c_root_lifetime_cashflow_conservation (h n : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (hm : total h p=1) (hn : n ≤ h) (hv : 0 < v) (hv1 : v ≤ 1) : (epv h v b p=massPV h v b p) ∧ (pure h n v p=pureMass h n v p) ∧ (endow h n v b p=term h n v b p+pure h n v p) ∧ (term h n v (fun _ => 1) p+pureMass h n v p+(1-v)*due h n v p=1) ∧ (second h v b p=secondMass h v b p) ∧ (endowSecond h n v b p=termSecond h n v b p+v^(2*n)*surv h p n) ∧ (epv h v b p+(1-v)*weightedDue h v b p+v^h*b (h-1)*surv h p h=differenceBenefit h v b p) ∧ (massPV h v (fun _ => 1) p=ActuarialFoundations.faM (massCohort h p) v h 0) ∧
(term h h v b p=term h n v b p+deferred h n (h-n) v b p) ∧
(delayEPV h 1 v b p=v*epv h v b p) ∧
(epv h v inc p+(1-v)*increasingDue h v p+(h : ℝ)*v^h*surv h p h=due h h v p) ∧
(0 < due h n v p → expectedLoss h n v (netPremium h n v b p) b p=0) := by sorry
