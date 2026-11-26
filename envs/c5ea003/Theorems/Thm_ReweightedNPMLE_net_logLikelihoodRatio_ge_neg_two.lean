-- Prove2me | Theorems.Thm_ReweightedNPMLE_net_logLikelihoodRatio_ge_neg_two
-- name    : ReweightedNPMLE.net_logLikelihoodRatio_ge_neg_two
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:53.4506+00:00
-- url     : https://prove2.me/theorems/d0f00f6d-0184-4189-b053-a85776b5494c
-- title:
--   Transferring near-optimal sample likelihood to an approximating net point
-- statement:
--   At $n$ sample points, let $p_i,q_i>0$ and let $\ell_i\in\mathbb R$ be candidate log scores; in the application, $\ell_i=\log f(X_i)$. Suppose
--   $$\sum_i\ell_i\ge\sum_i\log q_i-1,\qquad
--   |\log p_i-\ell_i|\le\delta\quad\text{for every }i,$$
--   and $n\delta\le1$. Then
--   $$\sum_i\log(p_i/q_i)\ge-2.$$
--   This is a deterministic calculation: no normalization, sampling law, or probability assumption is needed. It only uses the candidate's log scores, while positivity is required for the net and reference values appearing in the ratios.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteNet.lean#L201-L231

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.net_logLikelihoodRatio_ge_neg_two
    {Ω : Type*} {n : ℕ} (p f q : Ω → ℝ) (x : Fin n → Ω) (δ : ℝ)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i))
    (hnear : (∑ i, Real.log (q (x i))) - 1 ≤
      ∑ i, Real.log (f (x i)))
    (happrox : ∀ i,
      |Real.log (p (x i)) - Real.log (f (x i))| ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1) :
    -2 ≤ ∑ i, Real.log (p (x i) / q (x i)) := by sorry
