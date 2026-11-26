-- Prove2me | solution 1 for ReweightedNPMLE.finite_optimizer_directional_sensitivity_lower
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:16.037648+00:00
-- url     : https://prove2.me/submissions/f0e58fae-5e88-4410-93e2-5584ab131bd2

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
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
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_eventually_mem_finiteSimplex_add_smul_zeroSum
import Theorems.Thm_ReweightedNPMLE_finiteMixtureValue_add_smul_eq_mul_one_add_relative
import Theorems.Thm_ReweightedNPMLE_fittedValue_secondOrderExpansion_of_eventually
import Theorems.Thm_ReweightedNPMLE_likelihood_contact_on_finite_optimizer_support
import Theorems.Thm_ReweightedNPMLE_relativeDictionary_weighted_sum_eq_zero_of_contact
import Theorems.Thm_ReweightedNPMLE_secondOrderCoefficient_le
import Theorems.Thm_ReweightedNPMLE_weightedLogLikelihood_multiplicative_secondOrder

-- Inline helpers preserved from ReweightedNPMLE.Weights.
section
/-!
# Weighted likelihood and normalization

This file formalizes the deterministic normalization statements in Section 2.2 of the
paper.  Vectors are represented by functions on `Fin n`; this is the representation used
throughout the rest of the development.
-/

open scoped BigOperators

namespace ReweightedNPMLE























theorem total_pos {n : ℕ} [Nonempty (Fin n)] {w : Fin n → ℝ}
    (hw : ∀ i, 0 < w i) : 0 < total w := by
  classical
  exact Finset.sum_pos (fun i _ ↦ hw i) Finset.univ_nonempty





















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




  


@[simp] theorem likelihoodContactFunctional_apply {n : ℕ}
    (w v a : Fin n → ℝ) :
    likelihoodContactFunctional w v a =
      ∑ i, w i / (v i * total w) * a i := by
  simp [likelihoodContactFunctional]











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























































theorem likelihoodContactNumerator_eq_total_of_functional_eq_one
    {n : ℕ} [Nonempty (Fin n)] (w v a : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (hcontact : likelihoodContactFunctional w v a = 1) :
    likelihoodContactNumerator w v a = total w := by
  have hrewrite : likelihoodContactFunctional w v a =
      likelihoodContactNumerator w v a / total w := by
    rw [likelihoodContactFunctional_apply]
    unfold likelihoodContactNumerator
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hv i).ne', (total_pos hw).ne']
  rw [hrewrite] at hcontact
  field_simp [(total_pos hw).ne'] at hcontact
  exact hcontact

theorem finite_optimizer_full_support_raw_contact
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    ∀ j, ∑ i, w i * (A j i / v i) = total w := by
  intro j
  have hfun := likelihood_contact_on_finite_optimizer_support
    A v p w hw hp hvpos hApos hvmax j
      (by simp [coefficientSupport, (hpfull j).ne'])
  exact likelihoodContactNumerator_eq_total_of_functional_eq_one
    w v (A j) hw hvpos hfun







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





/-- Consequently every active zero-mass tangent gives a locally feasible
fitted-value path in the dictionary convex hull. -/
theorem eventually_multiplicative_tangent_mem_convexHull
    {k n : ℕ} (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (p : Fin k → ℝ) (hp : p ∈ finiteMixtureFiber A v)
    (hpfull : ∀ j, 0 < p j) (hv : ∀ i, v i ≠ 0)
    (c : zeroSumCoefficients k) :
    ∀ᶠ t : ℝ in nhds 0,
      (fun i ↦ v i * (1 + t * relativeDictionaryMap A v c.1 i)) ∈
        convexHull ℝ (Set.range A) := by
  filter_upwards [eventually_mem_finiteSimplex_add_smul_zeroSum p hp.1 hpfull c]
    with t ht
  rw [← finiteMixtureValue_add_smul_eq_mul_one_add_relative A v p hp.2 hv c.1 t]
  exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A _ ht



















end ReweightedNPMLE
end

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The core directional support-sensitivity inequality.  Every
mass-preserving active-support tangent is dominated by the Hessian quadratic
form of the fitted log map. -/
theorem solution
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (h : Fin n → ℝ) (c : zeroSumCoefficients k) :
    2 * ∑ i, h i * relativeDictionaryMap A v c.1 i -
        ∑ i, w i * (relativeDictionaryMap A v c.1 i) ^ 2 ≤
      ∑ i, h i * J h i := by
  let u : Fin n → ℝ := relativeDictionaryMap A v c.1
  let ell : ℝ := ∑ i, h i * Real.log (v i)
  let ac : ℝ := (∑ i, h i * u i) - (1 / 2 : ℝ) * ∑ i, w i * u i ^ 2
  let af : ℝ := (1 / 2 : ℝ) * ∑ i, h i * J h i
  let fc : ℝ → ℝ := fun t ↦
    weightedLogLikelihood (w + t • h) (fun i ↦ v i * (1 + t * u i)) -
      weightedLogLikelihood w v - t * ell - t ^ 2 * ac
  let ff : ℝ → ℝ := fun t ↦
    fittedOptimalValue vhat (w + t • h) - fittedOptimalValue vhat w -
      t * ell - t ^ 2 * af
  have hsubset : convexHull ℝ (Set.range A) ⊆ C := convexHull_min hA hC
  have hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v := by
    refine ⟨?_, ?_⟩
    · rw [← hp.2]
      exact finiteMixtureValue_mem_convexHull_of_mem_finiteSimplex A p hp.1
    · intro q hq
      simpa [hvw] using (hmax w).2 q (hsubset hq)
  have hcontact := finite_optimizer_full_support_raw_contact
    A v p w hw hp hpfull hvpos hApos hvmax
  have hwu : ∑ i, w i * u i = 0 := by
    exact relativeDictionary_weighted_sum_eq_zero_of_contact A v w hcontact c
  have hfc : fc =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
    have hcand := weightedLogLikelihood_multiplicative_secondOrder
      w h v u hvpos
    convert hcand using 1
    ext t
    dsimp [fc, ell, ac]
    rw [hwu]
    ring
  have hff : ff =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by
    have hfit := fittedValue_secondOrderExpansion_of_eventually
      (fittedOptimalValue vhat) (fun q i ↦ Real.log (vhat q i)) hpsi hz h
    convert hfit using 1
    ext t
    dsimp [ff, ell, af]
    rw [hvw]
    ring
  have hfeas := eventually_multiplicative_tangent_mem_convexHull
    A v p hp hpfull (fun i ↦ (hvpos i).ne') c
  have hdom : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      fc t + t ^ 2 * ac ≤ ff t + t ^ 2 * af := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hfeas] with t ht
    have hm := (hmax (w + t • h)).2
      (fun i ↦ v i * (1 + t * u i)) (hsubset ht)
    have hm' : weightedLogLikelihood (w + t • h)
        (fun i ↦ v i * (1 + t * u i)) ≤
        fittedOptimalValue vhat (w + t • h) := by
      simpa [fittedOptimalValue] using hm
    dsimp [fc, ff]
    have hbase : fittedOptimalValue vhat w = weightedLogLikelihood w v := by
      simp [fittedOptimalValue, hvw]
    rw [hbase]
    linarith
  have hab : ac ≤ af := secondOrderCoefficient_le fc ff ac af hfc hff hdom
  dsimp [ac, af, u] at hab ⊢
  linarith
