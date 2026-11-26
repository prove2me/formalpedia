-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurableSet_independentRepresentationEvent
-- name    : ReweightedNPMLE.measurableSet_independentRepresentationEvent
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:44.160741+00:00
-- url     : https://prove2.me/theorems/af46a727-7ad4-4092-9bba-e258ce48cfe9
-- title:
--   Borel measurability of an independent representation of fixed size
-- statement:
--   Let $D\subset\mathbb R^n$ be closed and let $\widehat v:\mathbb R^n\to\mathbb R^n$ be continuous on the positive orthant. For a fixed $k\in\mathbb N$, consider the weights $w>0$ for which there exist linearly independent vectors $a_1,\ldots,a_k\in D$ and coefficients $p_j>0$ satisfying
--   $$\sum_jp_j=1,\qquad\sum_jp_ja_j=\widehat v(w).$$
--   This set of weights is Borel measurable. The dictionary need not be finite or bounded, and no regularity of $\widehat v$ is required outside the positive orthant.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ExtremeSupport.lean#L35-L84

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Maximum independent optimizer support

This file defines the maximum cardinality of independent full-support finite
representations of a fitted vector.  The fixed-cardinality representation
events are measurable because their parameter sets are locally closed in
second-countable locally compact spaces and hence sigma-compact.  Projection
preserves sigma-compactness.  The maximum is attained when positive, is at
most the ambient dimension, and satisfies the canonical support-sensitivity
Jacobian bound.  Its identification with extreme mixing-measure supports is
a separate optimizer-fiber statement.
-/

open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.measurableSet_independentRepresentationEvent {n : ℕ}
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvcont : ContinuousOn vhat (positiveVectors n)) (k : ℕ) :
    MeasurableSet (independentRepresentationEvent D vhat k) := by sorry
