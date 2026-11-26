-- Prove2me | Theorems.Thm_ReweightedNPMLE_finite_density_net_likelihood_test_bound
-- name    : ReweightedNPMLE.finite_density_net_likelihood_test_bound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:43:10.024908+00:00
-- url     : https://prove2.me/theorems/ee9f9668-9d9e-51ba-b15e-ac75779cda19
-- title:
--   A uniform likelihood test over a finite Hellinger-separated net
-- statement:
--   Let $q$ be a measurable strictly positive probability density relative to a measure $\mu$, and let $(p_r)_{r\in N}$ be a finite collection of strictly positive probability densities. Assume all densities and affinities $\sqrt{p_rq}$ are integrable. If $H^2(p_r,q)\ge t^2$ for every $r\in N$, then under $n$ iid observations from $q$,
--   $$
--   P_n^*\!\left(\exists r\in N:\sum_i\log\frac{p_r(X_i)}{q(X_i)}\ge-2\right)
--   \le |N|\exp(1-nt^2/2).
--   $$
--   Here $t$ may be any real number, since only its square enters. The net cardinality is the sole multiplicative cost. Here $H^2(a,b)=\int(\sqrt a-\sqrt b)^2\,d\mu$, without a factor $1/2$.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteNet.lean#L166-L199

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

theorem ReweightedNPMLE.finite_density_net_likelihood_test_bound
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
      N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by sorry
