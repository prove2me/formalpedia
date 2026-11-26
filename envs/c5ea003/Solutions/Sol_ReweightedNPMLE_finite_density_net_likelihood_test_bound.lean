-- Prove2me | solution 1 for ReweightedNPMLE.finite_density_net_likelihood_test_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:07:24.484863+00:00
-- url     : https://prove2.me/submissions/a25d3be0-a72f-4485-a507-852230a9d733

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
import Theorems.Thm_ReweightedNPMLE_fixed_density_likelihood_ratio_test_bound
import Theorems.Thm_ReweightedNPMLE_measureReal_finset_test_union_le_card_mul

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
/-- Concrete finite-net likelihood test.  Every net density separated by at
least `t²` in squared Hellinger distance has its `logLR ≥ -2` event bounded
by the same exponential; a finite union costs exactly the net cardinality. -/
theorem solution
    {Ω ι : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (N : Finset ι) (p : ι → Ω → ℝ) (q : Ω → ℝ)
    (t : ℝ)
    (hqmeas : Measurable q) (hq : ∀ x, 0 < q x)
    (hqint : Integrable q μ) (hq_one : ∫ x, q x ∂μ = 1)
    (hp : ∀ r ∈ N, ∀ x, 0 < p r x)
    (hpint : ∀ r ∈ N, Integrable (p r) μ)
    (haint : ∀ r ∈ N, Integrable (fun x ↦ Real.sqrt (p r x * q x)) μ)
    (hp_one : ∀ r ∈ N, ∫ x, p r x ∂μ = 1)
    (hsep : ∀ r ∈ N, t ^ 2 ≤ hellingerSq μ (p r) q) :
    let ν := Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))
    ν.real (⋃ r ∈ N,
        {x | -2 ≤ ∑ i, Real.log (p r (x i) / q (x i))}) ≤
      N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  dsimp only
  apply measureReal_finset_test_union_le_card_mul
  · positivity
  · intro r hr
    calc
      (Measure.pi (fun _ : Fin n ↦
        μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
          {x | -2 ≤ ∑ i, Real.log (p r (x i) / q (x i))} ≤
          Real.exp (1 - (n : ℝ) * hellingerSq μ (p r) q / 2) :=
        fixed_density_likelihood_ratio_test_bound μ (p r) q hqmeas
          (hp r hr) hq (hpint r hr) hqint (haint r hr) (hp_one r hr) hq_one
      _ ≤ Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith [hsep r hr]
