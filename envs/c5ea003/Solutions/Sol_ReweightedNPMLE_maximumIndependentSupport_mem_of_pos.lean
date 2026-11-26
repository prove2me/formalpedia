-- Prove2me | solution 1 for ReweightedNPMLE.maximumIndependentSupport_mem_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:58.643562+00:00
-- url     : https://prove2.me/submissions/f8c632df-a934-4ce9-b7a3-b33f604c6af2

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
open ReweightedNPMLE in
theorem solution {n : ℕ}
    (D : Set (Fin n → ℝ)) (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ} (hw : 0 < maximumIndependentSupport D vhat w) :
    w ∈ independentRepresentationEvent D vhat (maximumIndependentSupport D vhat w) := by
  classical
  let f : ℕ → ℕ := fun k ↦ if w ∈ independentRepresentationEvent D vhat k then k else 0
  have hne : (Finset.range (n + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  obtain ⟨k, hk, heq⟩ := (Finset.sup_mem_of_nonempty (f := f) hne)
  have hkevent : w ∈ independentRepresentationEvent D vhat k := by
    by_contra hn
    have hz : f k = 0 := by simp [f, hn]
    change 0 < (Finset.range (n + 1)).sup f at hw
    rw [← heq, hz] at hw
    omega
  have hkeq : k = maximumIndependentSupport D vhat w := by
    simpa [f, maximumIndependentSupport, hkevent] using heq
  simpa [← hkeq] using hkevent
