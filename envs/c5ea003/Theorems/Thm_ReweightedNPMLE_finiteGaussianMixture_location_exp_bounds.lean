-- Prove2me | Theorems.Thm_ReweightedNPMLE_finiteGaussianMixture_location_exp_bounds
-- name    : ReweightedNPMLE.finiteGaussianMixture_location_exp_bounds
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:37:01.295271+00:00
-- url     : https://prove2.me/theorems/ad3c7a83-afe6-53b5-9904-b1d05b599e1a
-- title:
--   Multiplicative comparison after moving all mixture locations
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(f_{w,\theta}(x)=\sum_iw_i\phi_d(x-\theta_i)\) for a finite index set \(I\). Suppose \(w_i\ge0\), \(T,S,\varepsilon\ge0\), \(\|x\|\le T\), \(\|\theta_i\|,\|\eta_i\|\le S\), and \(\|\theta_i-\eta_i\|\le\varepsilon\) for every \(i\). Then
--   \[
--   e^{-(T+S)\varepsilon}f_{w,\theta}(x)
--   \le f_{w,\eta}(x)
--   \le e^{(T+S)\varepsilon}f_{w,\theta}(x).
--   \]
--   The same nonnegative weights are used before and after the perturbation. Their total mass need not be one.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L147-L182

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

theorem ReweightedNPMLE.finiteGaussianMixture_location_exp_bounds
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε) :
    Real.exp (-((T + S) * ε)) * finiteGaussianMixture w θ x ≤
        finiteGaussianMixture w η x ∧
      finiteGaussianMixture w η x ≤
        Real.exp ((T + S) * ε) * finiteGaussianMixture w θ x := by sorry
