-- Prove2me | Theorems.Thm_ReweightedNPMLE_hellingerSq_finiteGaussianMixture_same_weights_le_sum
-- name    : ReweightedNPMLE.hellingerSq_finiteGaussianMixture_same_weights_le_sum
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:55.449983+00:00
-- url     : https://prove2.me/theorems/ee8d0e3a-905b-4b04-9584-8810dd5dee7f
-- title:
--   Hellinger convexity for mixtures with common weights
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\), and for a finite index set \(I\) write \(f_{w,\theta}(x)=\sum_{i\in I}w_i\phi_d(x-\theta_i)\). Use the convention \(H^2(p,q)=\int_{\mathbb R^d}(\sqrt p-\sqrt q)^2\,dx\). For nonnegative weights \(w_i\) and any locations \(\theta_i,\eta_i\),
--   \[
--   H^2(f_{w,\theta},f_{w,\eta})
--   \le\sum_i w_iH^2\bigl(\phi_d(\,\cdot-\theta_i),\phi_d(\,\cdot-\eta_i)\bigr).
--   \]
--   The weights may have arbitrary total mass. In particular, a pairing of components bounds the global mixture discrepancy by the weighted sum of the corresponding component discrepancies.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureHellinger.lean#L578-L632

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

theorem ReweightedNPMLE.hellingerSq_finiteGaussianMixture_same_weights_le_sum {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) :
    hellingerSq volume (finiteGaussianMixture w θ)
        (finiteGaussianMixture w η) ≤
      ∑ i, w i * hellingerSq volume
        (fun x ↦ gaussianKernel d x (θ i))
        (fun x ↦ gaussianKernel d x (η i)) := by sorry
