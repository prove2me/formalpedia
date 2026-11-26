-- Prove2me | Theorems.Thm_ReweightedNPMLE_canonical_maximumIndependentSupport_jacobian_determinant_lower
-- name    : ReweightedNPMLE.canonical_maximumIndependentSupport_jacobian_determinant_lower
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:30.664227+00:00
-- url     : https://prove2.me/theorems/1de3b63d-a2fc-5521-b257-0a7fe5aa9742
-- title:
--   An exponential determinant lower bound from independent fitted support
-- statement:
--   Let $n\ge1$ and let $C\subset(0,\infty)^n$ be nonempty, compact, and convex, with $D\subset C$. For positive $w$, let $\widehat v(w)$ maximize $\sum_iw_i\log v_i$ over $C$, and suppose $z(w)=\log\widehat v(w)$ is Fréchet differentiable there with matrix $J$. Let $k(w)$ be the maximum size of an independent strictly positive convex representation of $\widehat v(w)$ from $D$, defaulting to zero. For any $0<a_i\le9/8$,
--   $$
--   \det\{\operatorname{diag}(a)+\operatorname{diag}(w)J\}
--   \ge\left(\prod_i a_i\right)(17/9)^{\max\{k(w)-1,0\}}.
--   $$
--   No closedness or convex-generation assumption is imposed on $D$.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ExtremeSupport.lean#L157-L206

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

theorem ReweightedNPMLE.canonical_maximumIndependentSupport_jacobian_determinant_lower
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^
      (maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by sorry
