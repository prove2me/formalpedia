-- Prove2me | Theorems.Thm_EntFunctional_toReal_klDiv_withDensity_eq_integral_mul_log
-- name    : EntFunctional.toReal_klDiv_withDensity_eq_integral_mul_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T03:53:28.35663+00:00
-- url     : https://prove2.me/theorems/abb5ab17-83ad-4d64-a534-e9149bde04ee
-- title:
--   KL of a density measure equals the entropy of the density
-- statement:
--   KL of a density measure equals the entropy of the density. For a probability measure $\mu$ and a measurable nonnegative density $g$ with $\int g\,d\mu = 1$, set $Q = \mu.\mathrm{withDensity}(g)$ (a probability measure with $Q \ll \mu$). Then the Kullback–Leibler divergence of $Q$ against $\mu$ equals the entropy functional $\int g \log g \, d\mu$. This is the bridge identity connecting Mathlib's `InformationTheory.klDiv` to the entropy functional $\mathrm{Ent}_\mu(f) = \int f\log f - (\int f)\log(\int f)$ of the entropy method: combined with the mass-normalization $f \mapsto f/\int f$ it computes $\mathrm{Ent}$ as a relative entropy, making KL tensorization (Han's inequality / sub-additivity, BLM Theorem 4.10) usable at the entropy-functional level.
-- source:
--   Boucheron, Lugosi, Massart, *Concentration Inequalities*, OUP 2013, §4.1 (Theorem 4.10 / Theorem 4.13: sub-additivity and the variational/duality characterization of entropy).

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open Real MeasureTheory
open scoped ENNReal NNReal

theorem EntFunctional.toReal_klDiv_withDensity_eq_integral_mul_log
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {g : α → ℝ}
    (hg_meas : Measurable g) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_int : Integrable g μ) (hg_mass : ∫ x, g x ∂μ = 1) :
    (InformationTheory.klDiv (μ.withDensity (fun x ↦ ENNReal.ofReal (g x))) μ).toReal
      = ∫ x, g x * log (g x) ∂μ := by sorry
