-- Prove2me | Theorems.Thm_ReweightedNPMLE_measurable_maximumIndependentSupport
-- name    : ReweightedNPMLE.measurable_maximumIndependentSupport
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:24.180699+00:00
-- url     : https://prove2.me/theorems/d768e924-2484-446d-adb8-7ae708c45991
-- title:
--   Measurability of the largest independent fitted representation
-- statement:
--   Let $D\subset\mathbb R^n$ be closed and let $\widehat v:\mathbb R^n\to\mathbb R^n$ be continuous on $(0,\infty)^n$. Define $k(w)$ as the maximum size of a linearly independent list from $D$ whose strictly positive convex combination equals $\widehat v(w)$, considering only positive $w$. Set $k(w)=0$ when no such representation exists, including outside the positive orthant. Then $k:\mathbb R^n\to\mathbb N$ is measurable. Only sizes $0,\ldots,n$ enter the maximum because an independent list in $\mathbb R^n$ has at most $n$ members.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ExtremeSupport.lean#L95-L110

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

theorem ReweightedNPMLE.measurable_maximumIndependentSupport {n : ℕ}
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvcont : ContinuousOn vhat (positiveVectors n)) :
    Measurable (maximumIndependentSupport D vhat) := by sorry
