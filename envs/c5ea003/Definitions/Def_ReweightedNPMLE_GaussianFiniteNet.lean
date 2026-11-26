-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
-- name    : ReweightedNPMLE_GaussianFiniteNet
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:24:51.193221+00:00
-- url     : https://prove2.me/theorems/5e3622f3-f03c-53ce-9524-8321eb54a05d
-- title:
--   Finite Gaussian mixture grids and moment-approximation errors
-- statement:
--   The order-\(2L\) moment dimension in \(\mathbb R^d\) is
--   \(k(d,L)=\binom{2L+d}{d}\), including the constant monomial. For location radius \(S\), sample radius \(T\), and \(a=TS+S^2/2\), define
--   \[
--   h_L(S)=\left[\frac{4e^{S^2}(S^2)^{2L+1}}{(2L+1)!}\right]^{1/2},
--   \qquad \rho_L(T,S)=\frac{2e^{2a}a^{L+1}}{(L+1)!}.
--   \]
--   These are the global squared-Hellinger and local relative-density error bounds used for moment matching. For a finite \(Q\subseteq\mathbb R^d\), the finite mixture grid contains all densities
--   \[
--   x\longmapsto\sum_{j=1}^{k+1}w_j(2\pi)^{-d/2}e^{-\|x-\theta_j\|^2/2}
--   \]
--   with \(\theta_j\in Q\) and \(w\) in the valid denominator-\(M\) simplex grid. Repeated locations and zero weights are allowed.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianFiniteNet.lean#L61-L83

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Archimedean
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
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite Gaussian-mixture grids

This module combines a finite location set with the denominator simplex grid.
It produces an actual finite set of Gaussian-mixture densities, proves the
entropy count used in the likelihood-net argument, and packages the local
log-density and global Hellinger rounding estimates for members of that set.
-/

open scoped BigOperators
open MeasureTheory

namespace ReweightedNPMLE













/-- Number of free nonconstant moments in the order-`2L` Carathéodory
construction. -/
noncomputable abbrev gaussianMomentDimension (d L : ℕ) : ℕ :=
  Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ)

/-- Global squared-Hellinger error of the order-`2L` moment-matched mixture. -/
noncomputable def gaussianMomentHellingerError (S : ℝ) (L : ℕ) : ℝ :=
  (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
    (2 * L + 1).factorial)) ^ (1 / 2 : ℝ)

/-- Local relative-density error of the order-`L` moment approximation. -/
noncomputable def gaussianMomentRelativeError (T S : ℝ) (L : ℕ) : ℝ :=
  2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
    ((T * S + S ^ 2 / 2) ^ (L + 1) / (L + 1).factorial)

/-- All `(k+1)`-component Gaussian mixtures whose locations belong to `Q`
and whose weights belong to the valid denominator-`M` simplex grid. -/
noncomputable def finiteGaussianMixtureGrid (d k M : ℕ)
    (Q : Finset (Point d)) : Finset (Point d → ℝ) := by
  classical
  exact ((Finset.univ : Finset (Fin (k + 1) → Q)).product
        (validSimplexWeightGrid k M)).image fun z ↦
      finiteGaussianMixture z.2 (fun i ↦ (z.1 i : Point d))



























end ReweightedNPMLE


