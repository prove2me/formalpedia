-- Prove2me | Theorems.Thm_ReweightedNPMLE_uniform_nearMLE_hellinger_bad_event_bound
-- name    : ReweightedNPMLE.uniform_nearMLE_hellinger_bad_event_bound
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:43:51.437262+00:00
-- url     : https://prove2.me/theorems/32d446ac-047c-4fda-99d1-f22d07afa135
-- title:
--   A finite likelihood net controls every Hellinger-distant near-maximizer
-- statement:
--   Let $q$ and $(p_r)_{r\in N}$ be strictly positive normalized integrable densities relative to $\mu$, with $q$ measurable and every $\sqrt{p_rq}$ integrable. Let $f_G$, $G\in\Gamma$, be strictly positive integrable candidate functions; their normalization is not assumed. For each $G$, choose $s(G)\in N$ with $H^2(f_G,p_{s(G)})\le g$. On a sample set $R$, assume
--   $$|\log p_{s(G)}(x_i)-\log f_G(x_i)|\le\delta$$
--   for all samples $x\in R$, candidates $G$, and coordinates $i$, with $n\delta\le1$. If the iid $q$ sample law satisfies $P_n^*(R^c)\le\rho$, then, for any real $t$,
--   $$
--   P_n^*\!\left(\exists G:\sum_i\log f_G(X_i)\ge\sum_i\log q(X_i)-1,\
--   H^2(f_G,q)>2g+2t^2\right)
--   \le\rho+|N|e^{1-nt^2/2}.
--   $$
--   Neither the selector nor the candidate-indexed bad event is assumed measurable. Here $H^2(a,b)=\int(\sqrt a-\sqrt b)^2\,d\mu$, without a factor $1/2$.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteNet.lean#L302-L425

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

theorem ReweightedNPMLE.uniform_nearMLE_hellinger_bad_event_bound
    {Ω ι Γ : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (N : Finset ι) (p : ι → Ω → ℝ)
    (q : Ω → ℝ) (f : Γ → Ω → ℝ) (select : Γ → ι)
    (radius : Set (Fin n → Ω)) (δ globalSq t radiusBound : ℝ)
    (hqmeas : Measurable q) (hq : ∀ x, 0 < q x)
    (hqint : Integrable q μ) (hq_one : ∫ x, q x ∂μ = 1)
    (hp : ∀ r ∈ N, ∀ x, 0 < p r x)
    (hpint : ∀ r ∈ N, Integrable (p r) μ)
    (haint : ∀ r ∈ N,
      Integrable (fun x ↦ Real.sqrt (p r x * q x)) μ)
    (hp_one : ∀ r ∈ N, ∫ x, p r x ∂μ = 1)
    (hf : ∀ G x, 0 < f G x) (hfint : ∀ G, Integrable (f G) μ)
    (hselect : ∀ G, select G ∈ N)
    (hglobal : ∀ G, hellingerSq μ (f G) (p (select G)) ≤ globalSq)
    (hlocal : ∀ x ∈ radius, ∀ G i,
      |Real.log (p (select G) (x i)) - Real.log (f G (x i))| ≤ δ)
    (hnδ : (n : ℝ) * δ ≤ 1)
    (hradius :
      (Measure.pi (fun _ : Fin n ↦
        μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real radiusᶜ ≤
          radiusBound) :
    (Measure.pi (fun _ : Fin n ↦
      μ.withDensity (fun y ↦ ENNReal.ofReal (q y)))).real
        {x | ∃ G,
          (∑ i, Real.log (q (x i))) - 1 ≤ ∑ i, Real.log (f G (x i)) ∧
          2 * globalSq + 2 * t ^ 2 < hellingerSq μ (f G) q} ≤
      radiusBound + N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by sorry
