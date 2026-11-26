-- Prove2me | solution 1 for ReweightedNPMLE.measurableSet_independentRepresentationEvent
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:21.367565+00:00
-- url     : https://prove2.me/submissions/7f1b088c-04ab-4363-babf-93022ac59b30

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

-- Inline helpers preserved from ReweightedNPMLE.FiniteOptimizerFiber.
section
/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE



theorem finiteSimplex_eq_stdSimplex (m : ℕ) :
    finiteSimplex m = stdSimplex ℝ (Fin m) := rfl

theorem isCompact_finiteSimplex (m : ℕ) : IsCompact (finiteSimplex m) := by
  rw [finiteSimplex_eq_stdSimplex]
  exact isCompact_stdSimplex ℝ (Fin m)













































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FittedRegularity.
section
/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

namespace ReweightedNPMLE

























theorem isOpen_positiveVectors (n : ℕ) : IsOpen (positiveVectors n) := by
  have heq : positiveVectors n = ⋂ i : Fin n, {w : Fin n → ℝ | 0 < w i} := by
    ext w
    simp [positiveVectors]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)

















end ReweightedNPMLE
end

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
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hvcont : ContinuousOn vhat (positiveVectors n)) (k : ℕ) :
    MeasurableSet (independentRepresentationEvent D vhat k) := by
  let U := positiveVectors n
  letI : LocallyCompactSpace U := (isOpen_positiveVectors n).locallyCompactSpace
  let X := U × ((Fin k → Fin n → ℝ) × (Fin k → ℝ))
  let O : Set X := {x | LinearIndependent ℝ x.2.1 ∧ x.2.2 ∈ positiveVectors k}
  let Z : Set X := {x | (∀ j, x.2.1 j ∈ D) ∧ x.2.2 ∈ finiteSimplex k ∧
    finiteMixtureValue x.2.1 x.2.2 = vhat x.1.val}
  have hO : IsOpen O := by
    exact (isOpen_setOf_linearIndependent.preimage
      (continuous_fst.comp continuous_snd)).inter
      ((isOpen_positiveVectors k).preimage (continuous_snd.comp continuous_snd))
  have hZ : IsClosed Z := by
    have hA : IsClosed {x : X | ∀ j, x.2.1 j ∈ D} := by
      have heq : {x : X | ∀ j, x.2.1 j ∈ D} = ⋂ j : Fin k, {x : X | x.2.1 j ∈ D} := by
        ext x
        simp
      rw [heq]
      exact isClosed_iInter fun j ↦ hDclosed.preimage
        ((continuous_apply j).comp (continuous_fst.comp continuous_snd))
    have hp : IsClosed {x : X | x.2.2 ∈ finiteSimplex k} :=
      (isCompact_finiteSimplex k).isClosed.preimage (continuous_snd.comp continuous_snd)
    have hf : Continuous (fun x : X ↦ finiteMixtureValue x.2.1 x.2.2) := by
      unfold finiteMixtureValue
      fun_prop
    have hg : Continuous (fun x : X ↦ vhat x.1.val) :=
      (continuousOn_iff_continuous_restrict.mp hvcont).comp continuous_fst
    exact hA.inter (hp.inter (isClosed_eq hf hg))
  let S := O ∩ Z
  have hSloc : IsLocallyClosed S := hO.isLocallyClosed.inter hZ.isLocallyClosed
  letI : LocallyCompactSpace S := hSloc.locallyCompactSpace
  have hsigma : IsSigmaCompact S := isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance
  let f : X → Fin n → ℝ := fun x ↦ x.1.val
  have himage : IsSigmaCompact (f '' S) := hsigma.image (continuous_subtype_val.comp continuous_fst)
  have heq : independentRepresentationEvent D vhat k = f '' S := by
    ext w
    constructor
    · rintro ⟨hw, A, hA, hlin, p, hp, hpfull, hvalue⟩
      refine ⟨(⟨w, hw⟩, A, p), ?_, rfl⟩
      exact ⟨⟨hlin, hpfull⟩, (fun j ↦ hA (mem_range_self j)), hp, hvalue⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.1.property, x.2.1, ?_, hx.1.1, x.2.2, hx.2.2.1, hx.1.2, hx.2.2.2⟩
      rintro a ⟨j, rfl⟩
      exact hx.2.1 j
  obtain ⟨K, hK, hKeq⟩ := himage
  rw [heq, ← hKeq]
  exact MeasurableSet.iUnion fun m ↦ (hK m).measurableSet
