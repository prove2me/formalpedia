-- Prove2me | solution 1 for ReweightedNPMLE.measureReal_finset_test_union_le_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:27.605451+00:00
-- url     : https://prove2.me/submissions/16260b3b-59ec-46bc-9cfc-02c2a2e54a51

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
/-- Real-valued version of the finite-union bound, convenient when the
pointwise likelihood-ratio estimates are stated using `Measure.real`. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset ι) (test : ι → Set Ω) (b : ℝ)
    (hb : 0 ≤ b) (htest : ∀ p ∈ N, μ.real (test p) ≤ b) :
    μ.real (⋃ p ∈ N, test p) ≤ N.card * b := by
  classical
  induction N using Finset.induction_on with
  | empty => simp
  | @insert p N hp ih =>
      rw [Finset.set_biUnion_insert]
      calc
        μ.real (test p ∪ ⋃ x ∈ N, test x) ≤
            μ.real (test p) + μ.real (⋃ x ∈ N, test x) :=
          measureReal_union_le _ _
        _ ≤ b + N.card * b := add_le_add (htest p (by simp))
          (ih (fun x hx ↦ htest x (by simp [hx])))
        _ = (insert p N).card * b := by
          rw [Finset.card_insert_of_notMem hp]
          push_cast
          ring
