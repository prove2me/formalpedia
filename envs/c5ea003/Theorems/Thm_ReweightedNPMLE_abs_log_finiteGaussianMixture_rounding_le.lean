-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_log_finiteGaussianMixture_rounding_le
-- name    : ReweightedNPMLE.abs_log_finiteGaussianMixture_rounding_le
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:34.770568+00:00
-- url     : https://prove2.me/theorems/62bcc687-569c-49fd-b847-08e99e92c9c5
-- title:
--   Local log-density error from rounding a finite mixture
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(f_{w,\theta}(x)=\sum_iw_i\phi_d(x-\theta_i)\) for a finite index set \(I\). Let \(w,v\) be probability vectors on \(I\). Suppose \(T,S,\varepsilon\ge0\), \(\|x\|\le T\), \(\|\theta_i\|,\|\eta_i\|\le S\), and \(\|\theta_i-\eta_i\|\le\varepsilon\) for every \(i\). Put \(B=TS+S^2/2\) and \(\Delta=\sum_i|v_i-w_i|\), and assume \(e^{2B}\Delta\le1/2\). Then
--   \[
--   |\log f_{v,\eta}(x)-\log f_{w,\theta}(x)|
--   \le(T+S)\varepsilon+2e^{2B}\Delta.
--   \]
--   This provides separate location and weight contributions to the log-density approximation on the observation ball.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L297-L333

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

theorem ReweightedNPMLE.abs_log_finiteGaussianMixture_rounding_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2) :
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (finiteGaussianMixture w θ x)| ≤
      (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| := by sorry
