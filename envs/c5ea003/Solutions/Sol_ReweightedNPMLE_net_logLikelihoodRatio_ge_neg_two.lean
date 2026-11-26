-- Prove2me | solution 1 for ReweightedNPMLE.net_logLikelihoodRatio_ge_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:29.163853+00:00
-- url     : https://prove2.me/submissions/dfb08a96-a643-4915-ad43-991aa02cec6b

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
open ReweightedNPMLE in
/-- Deterministic likelihood-transfer calculation from the paper: a candidate
within one log-likelihood unit of the truth and uniformly `δ`-approximated on
all sample points by a net density gives a net log-likelihood ratio at least
`-2`, provided `nδ ≤ 1`. -/
theorem solution
    {Ω : Type*} {n : ℕ} (p f q : Ω → ℝ) (x : Fin n → Ω) (δ : ℝ)
    (hp : ∀ i, 0 < p (x i)) (hq : ∀ i, 0 < q (x i))
    (hnear : (∑ i, Real.log (q (x i))) - 1 ≤
      ∑ i, Real.log (f (x i)))
    (happrox : ∀ i,
      |Real.log (p (x i)) - Real.log (f (x i))| ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1) :
    -2 ≤ ∑ i, Real.log (p (x i) / q (x i)) := by
  have hnet : (∑ i, Real.log (f (x i))) - (n : ℝ) * δ ≤
      ∑ i, Real.log (p (x i)) := by
    calc
      (∑ i, Real.log (f (x i))) - (n : ℝ) * δ =
          ∑ i, (Real.log (f (x i)) - δ) := by
        rw [Finset.sum_sub_distrib]
        simp
      _ ≤ ∑ i, Real.log (p (x i)) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := (abs_le.mp (happrox i)).1
        linarith
  rw [show (∑ i, Real.log (p (x i) / q (x i))) =
      (∑ i, Real.log (p (x i))) - ∑ i, Real.log (q (x i)) by
    simp_rw [Real.log_div (hp _).ne' (hq _).ne']
    exact Finset.sum_sub_distrib (s := Finset.univ)
      (fun i ↦ Real.log (p (x i))) (fun i ↦ Real.log (q (x i)))]
  linarith
