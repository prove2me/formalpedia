-- Prove2me | Definitions.Def_ReweightedNPMLE_SmallSupportProbability
-- name    : ReweightedNPMLE_SmallSupportProbability
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:25:20.948854+00:00
-- url     : https://prove2.me/theorems/ad0440e1-504e-58d0-a2b8-65fa25c2c10d
-- title:
--   Finite atomic probability laws with a prescribed atom budget
-- statement:
--   For a measurable space \(\Theta\) and an integer \(m\ge0\), define the finite-law map by
--   \[
--   ((a_1,\ldots,a_m),(w_1,\ldots,w_m))
--   \longmapsto\sum_{j=1}^m w_j\delta_{a_j},
--   \]
--   where \(a_j\in\Theta\), \(w_j\ge0\), and \(\sum_jw_j=1\).
--   The set of probability laws with atom budget \(m\) is the union of the ranges of these maps for \(k=0,\ldots,m\). Thus membership means that a law admits a representation using at most \(m\) atoms. Repeated locations and zero coefficients are allowed, so the representation need not list distinct support points or use all available slots.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SmallSupportProbability.lean#L18-L46

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Closed sets of probability laws with bounded finite support

The at-most-`m`-atom laws form a compact set in the weak topology. Finite
atomic laws are parameterized by compact atom lists and closed simplices,
including zero masses and coincident locations.
-/

open Set MeasureTheory
open scoped BigOperators Topology

namespace ReweightedNPMLE

noncomputable def finiteProbabilityLawMap {Θ : Type*} [MeasurableSpace Θ] (m : ℕ) :
    (Fin m → Θ) × (finiteSimplex m) → ProbabilityMeasure Θ :=
  fun p ↦ finiteProbabilityMeasure p.1 p.2.val p.2.property





noncomputable def smallSupportProbabilityLaws (Θ : Type*) [MeasurableSpace Θ] (m : ℕ) :
    Set (ProbabilityMeasure Θ) :=
  ⋃ k : Fin (m + 1), range (finiteProbabilityLawMap (Θ := Θ) (k : ℕ))







end ReweightedNPMLE


