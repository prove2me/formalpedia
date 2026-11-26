-- Prove2me | solution 1 for ReweightedNPMLE.exists_independentRepresentationEvent_of_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:44.523183+00:00
-- url     : https://prove2.me/submissions/3eb3787a-13d1-4844-8cf7-c3dbf08087c3

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
import Theorems.Thm_ReweightedNPMLE_augmented_linearIndepOn_iff_of_contact
import Theorems.Thm_ReweightedNPMLE_augmented_linearIndepOn_of_finiteMixtureFiber_extreme
import Theorems.Thm_ReweightedNPMLE_finiteMixtureFiber_extreme_of_augmented_linearIndepOn
import Theorems.Thm_ReweightedNPMLE_likelihood_contact_on_finite_optimizer_support

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





theorem continuous_finiteMixtureValue
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → E) : Continuous (finiteMixtureValue A) := by
  unfold finiteMixtureValue
  fun_prop





theorem isCompact_finiteMixtureFiber
    {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → E) (v : E) : IsCompact (finiteMixtureFiber A v) := by
  have hclosed : IsClosed {p | finiteMixtureValue A p = v} :=
    isClosed_eq (continuous_finiteMixtureValue A) continuous_const
  exact (isCompact_finiteSimplex m).inter_right hclosed





@[simp] theorem mem_coefficientSupport {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∈ coefficientSupport p ↔ p i ≠ 0 := by
  simp [coefficientSupport]

theorem not_mem_coefficientSupport_iff {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∉ coefficientSupport p ↔ p i = 0 := by
  simp [coefficientSupport]











/-- Characterization of the extreme points of a finite mixture fiber. -/
theorem finiteMixtureFiber_extreme_iff_augmented_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      p ∈ finiteMixtureFiber A v ∧
        LinearIndepOn ℝ (augmentedDictionary A)
          (coefficientSupport p : Set (Fin m)) := by
  constructor
  · intro hp
    exact ⟨hp.1, augmented_linearIndepOn_of_finiteMixtureFiber_extreme A v p hp⟩
  · rintro ⟨hp, hlin⟩
    exact finiteMixtureFiber_extreme_of_augmented_linearIndepOn A v p hp hlin





/-- With a contact functional, the paper's stated linear-independence
characterization of an extreme optimizer is exact. -/
theorem finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hcontact : ∀ i ∈ coefficientSupport p, b (A i) = 1) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      p ∈ finiteMixtureFiber A v ∧
        LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
  rw [finiteMixtureFiber_extreme_iff_augmented_linearIndepOn]
  exact and_congr_right fun _ ↦
    augmented_linearIndepOn_iff_of_contact A (coefficientSupport p) b hcontact







end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FittedContact.
section
/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE




  










/-- Exact finite-dictionary form of the paper's extreme-optimizer lemma:
under positive likelihood weights, an optimizing probability vector is
extreme precisely when its active evaluation vectors are linearly
independent. -/
theorem finite_likelihood_optimizer_extreme_iff_linearIndepOn
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
  have hcontact := likelihood_contact_on_finite_optimizer_support
    A v p w hw hp hvpos hApos hvmax
  rw [finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    A v p (likelihoodContactFunctional w v) hcontact, and_iff_right hp]



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



theorem fittedValueSelection_isMax {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n) (w : Fin n → ℝ) :
    IsMaxOn C (weightedLogLikelihood w)
      (fittedValueSelection C hCcompact hCnonempty hCpos w) :=
  Classical.choose_spec (exists_fittedValue_maximizer hCcompact hCnonempty hCpos w)







































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.SupportSensitivityAnalytic.
section
/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE



/-- A finite convex combination of dictionary atoms lies in their convex
hull. -/
theorem finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex
    {k : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin k → E) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k) :
    finiteMixtureValue A p ∈ convexHull ℝ (Set.range A) := by
  apply (convex_convexHull ℝ (Set.range A)).sum_mem (fun i _ ↦ hp.1 i) hp.2
  intro i _
  exact subset_convexHull ℝ (Set.range A) ⟨i, rfl⟩

























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
theorem solution
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hD : D ⊆ C)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hvHull : fittedValueSelection C hCcompact hCnonempty hCpos w ∈ convexHull ℝ D) :
    ∃ k : ℕ, w ∈ independentRepresentationEvent D
      (fittedValueSelection C hCcompact hCnonempty hCpos) k := by
  classical
  let v := fittedValueSelection C hCcompact hCnonempty hCpos w
  obtain ⟨ι, hι, p₀, A₀, hp₀, hpsum₀, hA₀, hvalue₀⟩ :=
    mem_convexHull_iff_exists_fintype.mp hvHull
  letI : Fintype ι := hι
  let m := Fintype.card ι
  let e : Fin m ≃ ι := (Fintype.equivFin ι).symm
  let A : Fin m → Fin n → ℝ := fun j ↦ A₀ (e j)
  let p : Fin m → ℝ := fun j ↦ p₀ (e j)
  have hp : p ∈ finiteMixtureFiber A v := by
    refine ⟨⟨fun j ↦ hp₀ (e j), ?_⟩, ?_⟩
    · exact (e.sum_comp p₀).trans hpsum₀
    · exact (e.sum_comp (fun j ↦ p₀ j • A₀ j)).trans hvalue₀
  have hA : Set.range A ⊆ D := by
    rintro a ⟨j, rfl⟩
    exact hA₀ (e j)
  obtain ⟨q, hqExt⟩ := (isCompact_finiteMixtureFiber A v).extremePoints_nonempty ⟨p, hp⟩
  have hq : q ∈ finiteMixtureFiber A v := hqExt.1
  have hvmax : IsMaxOn (convexHull ℝ (Set.range A)) (weightedLogLikelihood w) v := by
    refine ⟨?_, ?_⟩
    · rw [← hp.2]
      exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
    · intro b hb
      exact (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).2 b
        (convexHull_min (hA.trans hD) hC hb)
  have hlin := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
    A v q w hw hq (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
    (fun j ↦ hCpos (hD (hA (mem_range_self j)))) hvmax).mp hqExt
  let S := coefficientSupport q
  let k := Fintype.card S
  let f : Fin k ≃ S := (Fintype.equivFin S).symm
  let B : Fin k → Fin n → ℝ := fun j ↦ A (f j)
  let r : Fin k → ℝ := fun j ↦ q (f j)
  have hsum : (∑ j : S, q j) = 1 := by
    calc
      (∑ j : S, q j) = ∑ j ∈ S, q j := Finset.sum_coe_sort S q
      _ = ∑ j, q j := Finset.sum_subset (Finset.subset_univ S)
        (fun j _ hj ↦ (not_mem_coefficientSupport_iff q j).mp hj)
      _ = 1 := hq.1.2
  have hvalue : (∑ j : S, q j • A j) = v := by
    calc
      (∑ j : S, q j • A j) = ∑ j ∈ S, q j • A j :=
        Finset.sum_coe_sort S (fun j ↦ q j • A j)
      _ = ∑ j, q j • A j := Finset.sum_subset (Finset.subset_univ S)
        (fun j _ hj ↦ by rw [(not_mem_coefficientSupport_iff q j).mp hj, zero_smul])
      _ = v := hq.2
  have hBlin : LinearIndependent ℝ B := hlin.comp f f.injective
  refine ⟨k, hw, B, ?_, hBlin, r, ⟨?_, ?_⟩, ?_, ?_⟩
  · rintro b ⟨j, rfl⟩
    exact hA ⟨(f j).val, rfl⟩
  · intro j
    exact hq.1.1 (f j)
  · exact (f.sum_comp (fun j : S ↦ q j)).trans hsum
  · intro j
    exact lt_of_le_of_ne (hq.1.1 (f j))
      (Ne.symm ((mem_coefficientSupport q (f j)).mp (f j).property))
  · exact (f.sum_comp (fun j : S ↦ q j • A j)).trans hvalue
