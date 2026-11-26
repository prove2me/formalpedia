-- Prove2me | Theorems.Thm_ReweightedNPMLE_fixed_density_likelihood_ratio_test_bound
-- name    : ReweightedNPMLE.fixed_density_likelihood_ratio_test_bound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:42:44.620188+00:00
-- url     : https://prove2.me/theorems/19f5651d-e80f-4ed9-899b-abf0889dd09e
-- title:
--   A fixed-density likelihood test with a Hellinger exponent
-- statement:
--   Let $\mu$ be a measure and let $p,q$ be strictly positive integrable functions with $\int p\,d\mu=\int q\,d\mu=1$. Assume $q$ is measurable and $\sqrt{pq}$ is integrable. Draw $X_1,\ldots,X_n$ independently from the law $q\,d\mu$. With $H^2(p,q)=\int(\sqrt p-\sqrt q)^2\,d\mu$,
--   $$
--   P_n^*\!\left(\sum_i\log\frac{p(X_i)}{q(X_i)}\ge-2\right)
--   \le\exp\{1-nH^2(p,q)/2\}.
--   $$
--   The Hellinger convention has no factor $1/2$. The conclusion remains an outer-probability bound if the displayed test set is not measurable.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteNet.lean#L71-L123

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

theorem ReweightedNPMLE.fixed_density_likelihood_ratio_test_bound
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (p q : Ω → ℝ)
    (hqmeas : Measurable q) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ)
    (haint : Integrable (fun x ↦ Real.sqrt (p x * q x)) μ)
    (hp_one : ∫ x, p x ∂μ = 1) (hq_one : ∫ x, q x ∂μ = 1) :
    (Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
        {x | -2 ≤ ∑ i, Real.log (p (x i) / q (x i))} ≤
      Real.exp (1 - (n : ℝ) * hellingerSq μ p q / 2) := by sorry
