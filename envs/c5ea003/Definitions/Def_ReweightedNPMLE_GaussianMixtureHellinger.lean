-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
-- name    : ReweightedNPMLE_GaussianMixtureHellinger
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:24:16.912931+00:00
-- url     : https://prove2.me/theorems/ca61127b-503b-5a03-82f2-a6302fea423d
-- title:
--   Taylor remainder of the Gaussian exponential inner-product kernel
-- statement:
--   For \(\theta,\eta\in\mathbb R^d\) and a nonnegative integer \(L\), define
--   \[
--   \mathcal E_L(\theta,\eta)
--   =e^{\langle\theta,\eta\rangle}
--   -\sum_{\ell=0}^{L}\frac{\langle\theta,\eta\rangle^\ell}{\ell!}.
--   \]
--   This is the signed remainder of the exponential series after degree \(L\). The kernel \(e^{\langle\theta,\eta\rangle}\) arises in Gaussian overlap integrals, and the truncated part is a polynomial in either location variable. Separating this remainder permits moment matching to cancel the polynomial contribution in comparisons of Gaussian mixtures.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureHellinger.lean#L82-L85

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

namespace ReweightedNPMLE











/-- Remainder after truncating the exponential series in the inner product. -/
noncomputable def pointInnerExpRemainder {d : ℕ} (L : ℕ)
    (θ η : Point d) : ℝ :=
  Real.exp (inner ℝ θ η) - pointTruncatedInnerExp L θ η















































end ReweightedNPMLE


