-- Prove2me | Definitions.Def_ReweightedNPMLE_ExtremeSupport
-- name    : ReweightedNPMLE_ExtremeSupport
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:24:49.72469+00:00
-- url     : https://prove2.me/theorems/31614f97-4c81-4a77-a644-395c17686870
-- title:
--   Independent representation events and their maximum size
-- statement:
--   For a dictionary set \(D\subseteq\mathbb R^n\), a fitted-value map \(\widehat v:\mathbb R^n\to\mathbb R^n\), and \(k\in\mathbb N\), define \(E_k\) as the set of positive weight vectors \(w\) for which there are linearly independent vectors \(A_1,\ldots,A_k\in D\) and strictly positive coefficients \(p_j\) satisfying
--   \[
--   \sum_jp_j=1,\qquad
--   \widehat v(w)=\sum_jp_jA_j.
--   \]
--   The maximum independent support statistic is
--   \[
--   M_D(w)=\max\bigl(\{k\in\{0,\ldots,n\}:w\in E_k\}\cup\{0\}\bigr).
--   \]
--   The finite range is sufficient because a linearly independent family in \(\mathbb R^n\) has at most \(n\) elements. The statistic is zero when no such representation exists, in particular outside the positive weight orthant.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ExtremeSupport.lean#L25-L93

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

namespace ReweightedNPMLE

/-- Positive weights at which the fitted vector admits an independent
full-support representation using exactly `k` dictionary vectors. -/
def independentRepresentationEvent {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (k : ℕ) :
    Set (Fin n → ℝ) :=
  {w | w ∈ positiveVectors n ∧ ∃ A : Fin k → Fin n → ℝ,
    Set.range A ⊆ D ∧ LinearIndependent ℝ A ∧
      ∃ p : Fin k → ℝ, p ∈ finiteSimplex k ∧ (∀ j, 0 < p j) ∧
        finiteMixtureValue A p = vhat w}



/-- Maximum independent full-support representation size.  Its value is
zero when no such representation exists (in particular outside the positive
orthant). -/
noncomputable def maximumIndependentSupport {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ)) (w : Fin n → ℝ) : ℕ := by
  classical
  exact (Finset.range (n + 1)).sup
    (fun k ↦ if w ∈ independentRepresentationEvent D vhat k then k else 0)





















end ReweightedNPMLE


