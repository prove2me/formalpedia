-- Prove2me | Theorems.Thm_ReweightedNPMLE_hellingerSq_finiteGaussianMixture_rounding
-- name    : ReweightedNPMLE.hellingerSq_finiteGaussianMixture_rounding
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:34.557464+00:00
-- url     : https://prove2.me/theorems/1e14587d-6abe-4132-a7fc-7cb51fcf36ad
-- title:
--   Hellinger error from rounding locations and weights
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\), and for a finite index set \(I\) write \(f_{w,\theta}(x)=\sum_{i\in I}w_i\phi_d(x-\theta_i)\). Use the convention \(H^2(p,q)=\int_{\mathbb R^d}(\sqrt p-\sqrt q)^2\,dx\). Let \(w\) and \(v\) be probability vectors on the same finite index set. If \(\varepsilon\ge0\) and \(\|\theta_i-\eta_i\|\le\varepsilon\) for every \(i\), then
--   \[
--   H^2(f_{w,\theta},f_{v,\eta})
--   \le\frac{\varepsilon^2}{2}+2\sum_i|w_i-v_i|.
--   \]
--   Thus the approximation error separates into a quadratic location term and an \(\ell^1\) weight term, with no restriction on the magnitude of the atom locations.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureHellinger.lean#L688-L719

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE

theorem ReweightedNPMLE.hellingerSq_finiteGaussianMixture_rounding {d : ℕ}
    {ι : Type*} [Fintype ι] (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (hloc : ∀ i, ‖θ i - η i‖ ≤ ε) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture v η) ≤
      ε ^ 2 / 2 + 2 * ∑ i, |w i - v i| := by sorry
