-- Prove2me | Theorems.Thm_actuarial_c_cont_annual_settled_law_bridge
-- name    : actuarial_c_cont_annual_settled_law_bridge
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T21:39:02.222347+00:00
-- url     : https://prove2.me/theorems/5a1f8f71-1471-4bf2-ad95-e55db4db0b8f
-- title:
--   Annual year-end assurance equals a continuous lifetime law with matched policy-year death masses
-- statement:
--   Let μ be the actual probability distribution of nonnegative future lifetime T and let p_j be the μ-probability of death in policy year [j,j+1), for every j<h. Pay a unit benefit at the year end j+1, not immediately on death, and use the annual discount v=exp(−δ) induced by the continuous force δ. Then integration over the real death times and independent summation over annual mortality masses yield exactly the same present value. The equality of the *interval probabilities* is a modelling hypothesis; the equality of the *expected values* is the derived conclusion.
--
--   Mathematical relationship:
--
--   $$
--   \int_{\mathbb R}\sum_{j=0}^{h-1}e^{-\delta(j+1)}
--   \mathbf1_{\{j\le T<j+1\}}\,d\mu(T)
--   =\sum_{j=0}^{h-1}v^{j+1}p_j,\qquad v=e^{-\delta}.
--   $$
--
--   Intervals are left-closed and right-open, including death precisely at a policy anniversary in the following year. Death at the right-censoring horizon h earns no death claim within the insured years. This is an open Lean proof obligation, not an assumed EPV identity or an accepted proof.
-- source:
--   Original derived actuarial connection between real death instants and annual mortality mass (not a verbatim result). S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 5, Section 5.7, printed p. 71, plus Chapters 7–8 on fractional durations and time-of-death claim payment. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml. Dickson–Hardy–Waters (2020), Chapter 4, DOI 10.1017/9781108784184.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_cont_annualSettlementPV
import Definitions.Def_actuarial_c_massPV

open ActuarialAssurances.Continuous

open MeasureTheory

theorem actuarial_c_cont_annual_settled_law_bridge (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (h : ℕ) (delta v : ℝ)
    (p : ℕ → ℝ)
    (hv : v = Real.exp (-delta))
    (hyears : ∀ j : ℕ, j < h →
      (μ (Set.Ico (j : ℝ) ((j + 1 : ℕ) : ℝ))).toReal = p j) :
    (∫ t, annualSettlementPV h delta t ∂μ) =
      ActuarialAssurances.massPV h v (fun _ => 1) p := by sorry
