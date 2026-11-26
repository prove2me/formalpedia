-- Prove2me | solution 1 for ReweightedNPMLE.finite_extreme_optimizer_weighted_tangent_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:01:00.613877+00:00
-- url     : https://prove2.me/submissions/9288331d-196e-4acf-84f0-60db0b68c828

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
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























@[simp] theorem mem_coefficientSupport {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∈ coefficientSupport p ↔ p i ≠ 0 := by
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

-- Inline helpers preserved from ReweightedNPMLE.SupportSensitivity.
section
/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

namespace ReweightedNPMLE









theorem finrank_zeroSumCoefficients_add_one (k : ℕ) [Nonempty (Fin k)] :
    Module.finrank ℝ (zeroSumCoefficients k) + 1 = k := by
  have hne : coefficientTotalLinearMap k ≠ 0 := by
    intro hzero
    have happ := LinearMap.congr_fun hzero (fun _ : Fin k ↦ (1 : ℝ))
    simp [coefficientTotalLinearMap] at happ
    have hkpos : 0 < k := by
      simpa using (Fintype.card_pos : 0 < Fintype.card (Fin k))
    omega
  simpa [zeroSumCoefficients, Module.finrank_fin_fun] using
    Module.Dual.finrank_ker_add_one_of_ne_zero hne

theorem finrank_zeroSumCoefficients (k : ℕ) [Nonempty (Fin k)] :
    Module.finrank ℝ (zeroSumCoefficients k) = k - 1 := by
  have h := finrank_zeroSumCoefficients_add_one k
  omega



@[simp] theorem relativeDictionaryMap_apply {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (c : Fin k → ℝ) (i : Fin n) :
    relativeDictionaryMap A v c i = (∑ j, c j * A j i) / v i := rfl

theorem relativeDictionaryMap_injective {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0) :
    Function.Injective (relativeDictionaryMap A v) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro c hc
    have hzero : ∑ j, c j • A j = 0 := by
      funext i
      have hi := congrFun (show relativeDictionaryMap A v c = 0 from hc) i
      simp only [relativeDictionaryMap_apply, Pi.zero_apply, div_eq_zero_iff] at hi
      simpa [smul_eq_mul] using hi.resolve_right (hv i)
    have hc0 := (Fintype.linearIndependent_iff.mp hlin) c hzero
    simpa only [Submodule.mem_bot] using funext hc0
  · exact bot_le

















theorem weightedMassPreservingRelativeMap_injective {k n : ℕ}
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0)
    (hw : ∀ i, 0 < w i) :
    Function.Injective (weightedMassPreservingRelativeMap A v w) := by
  intro c d hcd
  apply Subtype.ext
  apply relativeDictionaryMap_injective A v hlin hv
  funext i
  have hi := congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) hcd
  change Real.sqrt (w i) * relativeDictionaryMap A v c.1 i =
    Real.sqrt (w i) * relativeDictionaryMap A v d.1 i at hi
  exact mul_left_cancel₀ (Real.sqrt_pos.2 (hw i)).ne' hi

theorem finrank_weightedRelativeTangentSpace {k n : ℕ} [Nonempty (Fin k)]
    (A : Fin k → Fin n → ℝ) (v w : Fin n → ℝ)
    (hlin : LinearIndependent ℝ A) (hv : ∀ i, v i ≠ 0)
    (hw : ∀ i, 0 < w i) :
    Module.finrank ℝ (weightedRelativeTangentSpace A v w) = k - 1 := by
  rw [weightedRelativeTangentSpace,
    LinearMap.finrank_range_of_inj
      (weightedMassPreservingRelativeMap_injective A v w hlin hv hw)]
  exact finrank_zeroSumCoefficients k



























end ReweightedNPMLE
end

/-!
# Finite-support tangent directions

This file formalizes the algebraic half of the paper's matrix-sensitivity
lemma.  Mass-preserving perturbations of a `k`-atom optimizer form a
`(k - 1)`-dimensional coefficient space.  A linearly independent evaluation
dictionary maps that space injectively to relative fitted-value directions.
After the square-root weight scaling, these directions remain
`(k - 1)`-dimensional, are orthogonal to the square-root weight vector by the
likelihood contact equations, and admit an explicit orthonormal matrix.
-/

open Set
open scoped BigOperators Matrix

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ) :
    Module.finrank ℝ (weightedRelativeTangentSpace A v w) = k - 1 := by
  have hlin : LinearIndependent ℝ A := by
    have hsupp : coefficientSupport p = Finset.univ := by
      ext j
      simp only [mem_coefficientSupport, Finset.mem_univ, iff_true]
      exact (hpfull j).ne'
    have hlinOn := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
      A v p w hw hp hvpos hApos hvmax).mp hextreme
    rw [hsupp] at hlinOn
    simpa using hlinOn
  exact finrank_weightedRelativeTangentSpace A v w hlin
    (fun i ↦ (hvpos i).ne') hw
