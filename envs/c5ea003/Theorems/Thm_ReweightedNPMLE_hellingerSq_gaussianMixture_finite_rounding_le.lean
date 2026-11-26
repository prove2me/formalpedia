-- Prove2me | Theorems.Thm_ReweightedNPMLE_hellingerSq_gaussianMixture_finite_rounding_le
-- name    : ReweightedNPMLE.hellingerSq_gaussianMixture_finite_rounding_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:43:14.275344+00:00
-- url     : https://prove2.me/theorems/c3464366-d224-4462-9712-9df732fffd91
-- title:
--   Global Hellinger transfer through finite-mixture rounding
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(f_{w,\theta}(x)=\sum_iw_i\phi_d(x-\theta_i)\) for a finite index set \(I\). Let \(p(x)=\int\phi_d(x-\vartheta(a))\,d\mu(a)\), with \(\mu\) a probability measure and \(\vartheta\) measurable. Let \(w,v\) be probability vectors, let \(\varepsilon\ge0\), and assume \(\|\theta_i-\eta_i\|\le\varepsilon\). Define \(H^2(p,q)=\int(\sqrt p-\sqrt q)^2dx\). If \(H^2(p,f_{w,\theta})\le\beta\), then
--   \[
--   H^2(p,f_{v,\eta})
--   \le2\beta+\varepsilon^2+4\sum_i|w_i-v_i|.
--   \]
--   Neither a bounded observation region nor bounded component locations are required.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L399-L433

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE

theorem ReweightedNPMLE.hellingerSq_gaussianMixture_finite_rounding_le
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {ε q : ℝ} (hε : 0 ≤ ε) (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hbase : hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
      (finiteGaussianMixture w θ) ≤ q) :
    hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture v η) ≤
      2 * q + ε ^ 2 + 4 * ∑ i, |w i - v i| := by sorry
