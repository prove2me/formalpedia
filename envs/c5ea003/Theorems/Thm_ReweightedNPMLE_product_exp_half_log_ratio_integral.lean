-- Prove2me | Theorems.Thm_ReweightedNPMLE_product_exp_half_log_ratio_integral
-- name    : ReweightedNPMLE.product_exp_half_log_ratio_integral
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:42:13.340571+00:00
-- url     : https://prove2.me/theorems/3b5079f9-06cd-40ea-9d36-12d33fbfb586
-- title:
--   Product factorization of a square-root likelihood-ratio integral
-- statement:
--   Let $\nu$ be a sigma-finite measure, $n\ge0$, and $p,q:\Omega\to\mathbb R$. Then $$\int_{\Omega^n}\exp\!\left(\tfrac12\sum_{i=1}^n\log\frac{p(x_i)}{q(x_i)}\right)d\nu^{\otimes n}=\left[\int_\Omega\exp\!\left(\tfrac12\log\frac{p(y)}{q(y)}\right)d\nu\right]^n.$$ This formal identity uses Lean’s total logarithm, division, and Bochner integral; positivity, measurability, and integrability are not additional hypotheses of this lemma. For positive densities it supplies the iid affinity factorization.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/Hellinger.lean#L503-L521

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.product_exp_half_log_ratio_integral {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) [SigmaFinite ν] (p q : Ω → ℝ) :
    ∫ x : Fin n → Ω,
        Real.exp ((∑ i, Real.log (p (x i) / q (x i))) / 2)
        ∂Measure.pi (fun _ : Fin n ↦ ν) =
      (∫ y, Real.exp (Real.log (p y / q y) / 2) ∂ν) ^ n := by sorry
