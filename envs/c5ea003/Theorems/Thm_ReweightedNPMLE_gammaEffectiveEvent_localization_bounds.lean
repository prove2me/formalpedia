-- Prove2me | Theorems.Thm_ReweightedNPMLE_gammaEffectiveEvent_localization_bounds
-- name    : ReweightedNPMLE.gammaEffectiveEvent_localization_bounds
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:26.76175+00:00
-- url     : https://prove2.me/theorems/035435c1-0ea5-47de-bfca-54ddc194e94c
-- title:
--   Explicit localization bounds on the Gamma effective event
-- statement:
--   Put $Q=q+\log(2n)$, $N=r\log5+q$, $A=\|P_V(w-\mathbf1)\|_2$, and $E=\eta\|w-\mathbf1\|_2$. Suppose $Q,N,\eta\ge0$, $\alpha>0$, $\eta\sqrt{\alpha nQ}\le1$, $1024Q\le\alpha$, $2359296N\le\alpha$, and $12288\le\alpha$. If $\|w-\mathbf1\|_\infty\le2\sqrt{Q/\alpha}$ and $\sqrt\alpha A\le4\sqrt N$, then all $w_i>0$ and $$\|w-\mathbf1\|_\infty\le1/16,\quad\alpha A^2\le16N,\quad\alpha E\le2,\quad A\le1/384,\quad E\le1/6144.$$ These are deterministic bounds; no distributional or rank hypothesis is required here.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaEffectiveEvent.lean#L103-L169

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Common Gamma concentration and localization event

The projected-energy and maximum-coordinate bounds hold jointly with
failure probability at most `2 exp(-q)`.  Explicit scale conditions imply
all radial localization hypotheses and the sharp `alpha E <= 2` width
cost bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.gammaEffectiveEvent_localization_bounds {n r : ℕ}
    {α q η : ℝ} (hα : 0 < α) (hQ : 0 ≤ effectiveQ n q) (hN : 0 ≤ effectiveN r q)
    (hη : 0 ≤ η) (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {w : Fin n → ℝ} (hw : w ∈ gammaEffectiveEvent V r α q) :
    let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    let E := η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
    (∀ i, |w i - 1| ≤ 1 / 16) ∧ w ∈ positiveVectors n ∧
    α * A ^ 2 ≤ 16 * effectiveN r q ∧ α * E ≤ 2 ∧
    A ≤ (1 / 16 : ℝ) / 24 ∧ E ≤ (1 / 16 : ℝ) ^ 2 / 24 := by sorry
