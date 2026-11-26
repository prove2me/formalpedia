-- Prove2me | solution 1 for ReweightedNPMLE.uniform_nearMLE_hellinger_bad_event_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:08:07.233433+00:00
-- url     : https://prove2.me/submissions/5a2d26f4-0958-40b0-980d-db49d11e3e17

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
import Theorems.Thm_ReweightedNPMLE_finite_density_net_likelihood_test_bound
import Theorems.Thm_ReweightedNPMLE_net_logLikelihoodRatio_ge_neg_two

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE

















/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]











/-- A squared triangle bound requiring only integrability of the three
square-root differences.  It is sufficient for the finite-net transfer and
avoids introducing an additional square-root-distance wrapper. -/
theorem hellingerSq_triangle_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q r : Ω → ℝ)
    (hpq : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hqr : Integrable (fun x ↦ (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2) μ)
    (hpr : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2) μ) :
    hellingerSq μ p r ≤ 2 * hellingerSq μ p q + 2 * hellingerSq μ q r := by
  unfold hellingerSq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hpq.const_mul 2) (hqr.const_mul 2)]
  apply integral_mono_ae hpr ((hpq.const_mul 2).add (hqr.const_mul 2))
  exact Filter.Eventually.of_forall fun x ↦ by
    change (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2 ≤
      2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 +
        2 * (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2
    nlinarith [sq_nonneg ((Real.sqrt (p x) - Real.sqrt (q x)) -
      (Real.sqrt (q x) - Real.sqrt (r x)))]



























end ReweightedNPMLE
end

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
/-- Concrete uniform near-MLE theorem for an arbitrary finite density net.
On a supplied radius event, every candidate has a selected net density with
local log error `δ` and global squared-Hellinger error `globalSq`.  The bad
near-MLE event is then controlled by the radius failure probability plus the
finite square-root likelihood-ratio union bound. -/
theorem solution
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
      radiusBound + N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  classical
  let ν₀ : Measure Ω := μ.withDensity (fun y ↦ ENNReal.ofReal (q y))
  letI : IsProbabilityMeasure ν₀ := IsProbabilityMeasure.mk (by
    dsimp [ν₀]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqint
        (Filter.Eventually.of_forall fun x ↦ (hq x).le), hq_one]
    norm_num)
  let ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n ↦ ν₀)
  letI : IsProbabilityMeasure ν := Measure.pi.instIsProbabilityMeasure _
  let Nfar := N.filter fun r ↦ t ^ 2 < hellingerSq μ (p r) q
  let test : ι → Set (Fin n → Ω) := fun r ↦
    {x | -2 ≤ ∑ i, Real.log (p r (x i) / q (x i))}
  have htestBound :
      ν.real (⋃ r ∈ Nfar, test r) ≤
        Nfar.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
    exact finite_density_net_likelihood_test_bound μ Nfar p q t hqmeas hq
      hqint hq_one
      (fun r hr ↦ hp r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ hpint r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ haint r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ hp_one r (Finset.mem_filter.mp hr).1)
      (fun r hr ↦ (Finset.mem_filter.mp hr).2.le)
  have hsubset :
      {x | ∃ G,
        (∑ i, Real.log (q (x i))) - 1 ≤ ∑ i, Real.log (f G (x i)) ∧
        2 * globalSq + 2 * t ^ 2 < hellingerSq μ (f G) q} ⊆
        radiusᶜ ∪ ⋃ r ∈ Nfar, test r := by
    rintro x ⟨G, hnear, hbad⟩
    by_cases hx : x ∈ radius
    · right
      have hrN : select G ∈ N := hselect G
      have hfar : t ^ 2 < hellingerSq μ (p (select G)) q := by
        by_contra hnot
        have hpqle : hellingerSq μ (p (select G)) q ≤ t ^ 2 := le_of_not_gt hnot
        have hfp : Integrable (fun y ↦
            (Real.sqrt (f G y) - Real.sqrt (p (select G) y)) ^ 2) μ :=
          hellingerIntegrand_integrable_of_integrable μ (f G) (p (select G))
            (hfint G).aestronglyMeasurable (hpint _ hrN).aestronglyMeasurable
            (Filter.Eventually.of_forall fun y ↦ (hf G y).le)
            (Filter.Eventually.of_forall fun y ↦ (hp _ hrN y).le)
            (hfint G) (hpint _ hrN)
        have hpq : Integrable (fun y ↦
            (Real.sqrt (p (select G) y) - Real.sqrt (q y)) ^ 2) μ :=
          hellingerIntegrand_integrable_of_integrable μ (p (select G)) q
            (hpint _ hrN).aestronglyMeasurable hqint.aestronglyMeasurable
            (Filter.Eventually.of_forall fun y ↦ (hp _ hrN y).le)
            (Filter.Eventually.of_forall fun y ↦ (hq y).le)
            (hpint _ hrN) hqint
        have hfq : Integrable (fun y ↦
            (Real.sqrt (f G y) - Real.sqrt (q y)) ^ 2) μ :=
          hellingerIntegrand_integrable_of_integrable μ (f G) q
            (hfint G).aestronglyMeasurable hqint.aestronglyMeasurable
            (Filter.Eventually.of_forall fun y ↦ (hf G y).le)
            (Filter.Eventually.of_forall fun y ↦ (hq y).le)
            (hfint G) hqint
        have htri := hellingerSq_triangle_bound
          μ (f G) (p (select G)) q hfp hpq hfq
        have htri' : hellingerSq μ (f G) q ≤
            2 * globalSq + 2 * t ^ 2 :=
          htri.trans (add_le_add
            (mul_le_mul_of_nonneg_left (hglobal G) (by norm_num))
            (mul_le_mul_of_nonneg_left hpqle (by norm_num)))
        exact (not_lt_of_ge htri') hbad
      have hlr := net_logLikelihoodRatio_ge_neg_two
        (p (select G)) (f G) q x δ
        (fun i ↦ hp _ hrN (x i)) (fun i ↦ hq (x i)) hnear
        (hlocal x hx G) hnδ
      simp only [Set.mem_iUnion]
      exact ⟨select G, ⟨Finset.mem_filter.mpr ⟨hrN, hfar⟩, hlr⟩⟩
    · left
      exact hx
  calc
    ν.real {x | ∃ G,
        (∑ i, Real.log (q (x i))) - 1 ≤ ∑ i, Real.log (f G (x i)) ∧
        2 * globalSq + 2 * t ^ 2 < hellingerSq μ (f G) q} ≤
        ν.real (radiusᶜ ∪ ⋃ r ∈ Nfar, test r) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ ν.real radiusᶜ + ν.real (⋃ r ∈ Nfar, test r) :=
      measureReal_union_le _ _
    _ ≤ radiusBound +
        Nfar.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) :=
      add_le_add hradius htestBound
    _ ≤ radiusBound + N.card * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
      have hcard : (Nfar.card : ℝ) ≤ N.card := by
        exact_mod_cast Finset.card_filter_le N _
      have hmul :
          (Nfar.card : ℝ) * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) ≤
            (N.card : ℝ) * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      linarith
