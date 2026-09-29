-- Prove2me | Theorems.Thm_HerbstGeneral_ratio_le_integral
-- name    : HerbstGeneral.ratio_le_integral
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-23T03:23:46.629984+00:00
-- url     : https://prove2.me/theorems/09d5709b-e4a8-45f1-90c3-7b6a4bbe0ef2
-- title:
--   BLM Lemma 6.25: generalized Herbst integration lemma
-- statement:
--   **Generalized Herbst integration lemma** (Boucheron–Lugosi–Massart, *Concentration Inequalities*, OUP 2013, Lemma 6.25). Right-derivative form: if $\rho$ is continuous on $[0,\lambda]$ with right derivative $\rho'$ on $[0,\lambda)$ bounded above by a continuous function $g$, then $\rho(\lambda) \le \rho(0) + \int_0^\lambda g$. This is the integration step that turns the differential inequality $f G' - f' G \le f^2 g$ (with $\rho = G/f$, by the quotient rule) into the cgf bound used in the proof of Bousquet's inequality (Theorem 12.5) for suprema of empirical processes. The classical Herbst argument ($f(\lambda)=\lambda$) is the special case; the general $f$ yields the Bennett $\log(1+u)$ exponent.
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities (OUP 2013), Lemma 6.25 (p.189-190); used in the proof of Theorem 12.5 (Bousquet's inequality), Section 12.4.

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
open Set Filter Topology intervalIntegral MeasureTheory

theorem HerbstGeneral.ratio_le_integral
    (ρ ρ' g : ℝ → ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hρ_cont : ContinuousOn ρ (Set.Icc 0 lam))
    (hg_cont : Continuous g)
    (hρ_deriv : ∀ x ∈ Set.Ico (0 : ℝ) lam, HasDerivWithinAt ρ (ρ' x) (Set.Ici x) x)
    (hbound : ∀ x ∈ Set.Ico (0 : ℝ) lam, ρ' x ≤ g x) :
    ρ lam ≤ ρ 0 + ∫ x in (0:ℝ)..lam, g x := by sorry
