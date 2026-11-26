-- Prove2me | Definitions.Def_ReweightedNPMLE_DirichletIndependence
-- name    : ReweightedNPMLE_DirichletIndependence
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:16:35.347989+00:00
-- url     : https://prove2.me/theorems/fb38439b-b26e-4c0b-9ddf-31cc4449ddf8
-- title:
--   Product Gamma laws and their densities
-- statement:
--   For \(n\) coordinates and Gamma shape and rate parameters \(a,r\), define the product measure
--   \[
--   \Gamma_{n,a,r}=\bigotimes_{i=1}^n\operatorname{Gamma}(a,r).
--   \]
--   Its extended-nonnegative density is the product of the coordinate Gamma densities, and its real density is the corresponding product of real-valued Gamma density functions. For \(a,r>0\), these are the law and density of independent Gamma coordinates, with
--   \[
--   g_{a,r}(t)=
--   \begin{cases}
--   r^a\,t^{a-1}e^{-rt}/\Gamma(a),&t\ge0,\\
--   0,&t<0.
--   \end{cases}
--   \qquad
--   g_{n,a,r}(w)=\prod_i g_{a,r}(w_i).
--   \]
--   The endpoint uses the real-power convention of the formal definition; its value does not affect the resulting measure.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/DirichletIndependence.lean#L114-L202

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Scale invariance behind Gamma--Dirichlet independence

The normalized Gamma vector is unchanged by a common positive rescaling.
This file first proves the corresponding exact scaling laws for scalar and
finite-product Gamma measures.  These are the measure-theoretic core of the
remaining independence statement in Proposition 2.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ReweightedNPMLE





/-- Product law of independent shape `a`, rate `r` Gamma coordinates. -/
noncomputable def gammaProductMeasure (n : ℕ) (a r : ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n ↦ gammaMeasure a r)





/-- Product density of independent shape `a`, rate `r` Gamma coordinates. -/
noncomputable def gammaProductDensity (n : ℕ) (a r : ℝ)
    (w : Fin n → ℝ) : ENNReal :=
  ∏ i, gammaPDF a r (w i)

/-- Real-valued version of the product Gamma density. -/
noncomputable def gammaProductDensityReal (n : ℕ) (a r : ℝ)
    (w : Fin n → ℝ) : ℝ :=
  ∏ i, gammaPDFReal a r (w i)



































end ReweightedNPMLE


