-- Prove2me | solution 1 for ReweightedNPMLE.canonical_maximumIndependentSupport_jacobian_determinant_lower
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:59.329818+00:00
-- url     : https://prove2.me/submissions/b4e5949b-fae7-4a67-8310-515077f36466

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
import Theorems.Thm_ReweightedNPMLE_coordinateLog_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_det_diagonal_add_weight_mul_eq_sqrt_conj
import Theorems.Thm_ReweightedNPMLE_det_mono_of_posDef_of_sub_posSemidef
import Theorems.Thm_ReweightedNPMLE_exists_local_positive_weight_lower_bound
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds
import Theorems.Thm_ReweightedNPMLE_finiteMixtureFiber_extreme_of_linearIndepOn
import Theorems.Thm_ReweightedNPMLE_finite_extreme_optimizer_hessian_determinant_lower
import Theorems.Thm_ReweightedNPMLE_fittedLogDerivativeMatrix_isHermitian_of_eventually
import Theorems.Thm_ReweightedNPMLE_fittedLogDerivative_quadratic_nonneg
import Theorems.Thm_ReweightedNPMLE_fittedOptimalValue_hasFDerivAt
import Theorems.Thm_ReweightedNPMLE_fittedValue_lipschitzOn
import Theorems.Thm_ReweightedNPMLE_maximumIndependentSupport_mem_of_pos

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













/-- Quantitative local Lipschitz bound for the fitted log-vector. -/
theorem fittedLog_lipschitzOn {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)} {a c B : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ w ∈ s, ∀ i, a ≤ w i)
    (hvc : ∀ w ∈ s, ∀ i, c ≤ vhat w i)
    (hvB : ∀ w ∈ s, ∀ i, vhat w i ≤ B)
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    LipschitzOnWith
      ⟨((n : ℝ) * B ^ 2 / (a * c)) / c, by positivity⟩
      (fun w i ↦ Real.log (vhat w i)) s := by
  exact coordinateLog_lipschitzOn vhat hc hvc
    (fittedValue_lipschitzOn hC hCpos vhat ha hc hB hwa hvc hvB hmax)







theorem isOpen_positiveVectors (n : ℕ) : IsOpen (positiveVectors n) := by
  have heq : positiveVectors n = ⋂ i : Fin n, {w : Fin n → ℝ | 0 < w i} := by
    ext w
    simp [positiveVectors]
  rw [heq]
  exact isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (continuous_apply i)

















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FittedEnvelope.
section
/-!
# Envelope theorem for fitted likelihood values

The optimized weighted likelihood is a convex function of the weight vector.
The two optimizer inequalities squeeze its first-order remainder between zero
and a product involving the change in the fitted log-vector.  Consequently,
continuity of the fitted log-vector implies that it is the Fréchet derivative
of the optimal-value function.  Combining this envelope argument with the
local Lipschitz estimates from `FittedRegularity` gives the paper's gradient
identity on every locally bounded positive weight box.
-/

open Set Filter Asymptotics
open scoped BigOperators Topology

namespace ReweightedNPMLE



















theorem canonicalFittedOptimalValue_hasFDerivAt {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty) (hCpos : C ⊆ positiveVectors n)
    (w : Fin n → ℝ)
    (hzcont : ContinuousAt
      (fittedLogSelection C hCcompact hCnonempty hCpos) w) :
    HasFDerivAt
      (fittedOptimalValue
        (fittedValueSelection C hCcompact hCnonempty hCpos))
      (fittedLogLinearFunctional
        (fittedLogSelection C hCcompact hCnonempty hCpos w)) w := by
  exact fittedOptimalValue_hasFDerivAt
    (fittedValueSelection C hCcompact hCnonempty hCpos) w
    (fun u ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos u)
    hzcont

theorem canonicalFittedOptimalValue_hasFDerivAt_of_local_bounds
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    {s : Set (Fin n → ℝ)} {w : Fin n → ℝ} (hws : s ∈ 𝓝 w)
    {a c B : ℝ} (ha : 0 < a) (hc : 0 < c) (hB : 0 < B)
    (hwa : ∀ u ∈ s, ∀ i, a ≤ u i)
    (hvc : ∀ u ∈ s, ∀ i,
      c ≤ fittedValueSelection C hCcompact hCnonempty hCpos u i)
    (hvB : ∀ u ∈ s, ∀ i,
      fittedValueSelection C hCcompact hCnonempty hCpos u i ≤ B) :
    HasFDerivAt
      (fittedOptimalValue
        (fittedValueSelection C hCcompact hCnonempty hCpos))
      (fittedLogLinearFunctional
        (fittedLogSelection C hCcompact hCnonempty hCpos w)) w := by
  apply canonicalFittedOptimalValue_hasFDerivAt
  have hlip := fittedLog_lipschitzOn hC hCpos
    (fittedValueSelection C hCcompact hCnonempty hCpos)
    ha hc hB hwa hvc hvB
    (fun u _hu ↦ fittedValueSelection_isMax
      C hCcompact hCnonempty hCpos u)
  exact hlip.continuousOn.continuousAt hws

/-- The canonical envelope identity at every positive weight.  Compact
positive fitted sets automatically provide all local coordinate bounds. -/
theorem canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    HasFDerivAt
      (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
      (fittedLogLinearFunctional (fittedLogSelection C hCcompact hCnonempty hCpos w)) w := by
  obtain ⟨c, B, hc, hB, hbound⟩ := exists_uniform_positive_coordinate_bounds hCcompact hCpos
  obtain ⟨a, ha, s, hs, hwa⟩ := exists_local_positive_weight_lower_bound w hw
  apply canonicalFittedOptimalValue_hasFDerivAt_of_local_bounds C hC hCcompact hCnonempty hCpos
    hs ha hc hB hwa
  · intro u _ i
    exact (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).1
  · intro u _ i
    exact (hbound _ (fittedValueSelection_isMax C hCcompact hCnonempty hCpos u).1 i).2

theorem eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    {n : ℕ} [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (w : Fin n → ℝ) (hw : w ∈ positiveVectors n) :
    ∀ᶠ q in nhds w,
      HasFDerivAt
        (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
        (fittedLogLinearFunctional (fittedLogSelection C hCcompact hCnonempty hCpos q)) q := by
  filter_upwards [(isOpen_positiveVectors n).mem_nhds hw] with q hq
  exact canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
    C hC hCcompact hCnonempty hCpos q hq

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FittedHessian.
section
/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

namespace ReweightedNPMLE



























@[simp] theorem fittedLogDerivativeMatrix_mulVec {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) (h : Fin n → ℝ) :
    fittedLogDerivativeMatrix J *ᵥ h = J h := by
  exact LinearMap.toMatrix'_mulVec J.toLinearMap h







theorem fittedLogDerivativeMatrix_posSemidef_of_eventually
    {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    (psi : (Fin n → ℝ) → ℝ) {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w, HasFDerivAt psi
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat u i))) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J w) :
    (fittedLogDerivativeMatrix J).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact fittedLogDerivativeMatrix_isHermitian_of_eventually psi
      (fun u i ↦ Real.log (vhat u i)) hpsi hz
  · intro h
    rw [fittedLogDerivativeMatrix_mulVec]
    simp only [star_trivial]
    simpa [dotProduct, mul_comm] using
      fittedLogDerivative_quadratic_nonneg vhat hmax hz h

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

























/-- The same determinant gain for the paper's nonsymmetric Jacobian matrix
`diag(a) + diag(w) Dz`. -/
theorem finite_extreme_optimizer_jacobian_determinant_lower
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by
  rw [det_diagonal_add_weight_mul_eq_sqrt_conj w a hw]
  exact finite_extreme_optimizer_hessian_determinant_lower
    A v p w hw hp hpfull hvpos hApos hextreme vhat hC hA hmax hvw hpsi hz
      a ha0 haUpper

/-- Canonical fitted-value version of the Jacobian bound.  The envelope
identity and positivity of the fitted vector are consequences of compact
positive convex feasibility, not additional analytic assumptions. -/
theorem canonical_finite_extreme_optimizer_jacobian_determinant_lower
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (A : Fin k → Fin n → ℝ) (hA : Set.range A ⊆ C)
    (p : Fin k → ℝ) (w : Fin n → ℝ) (hw : w ∈ positiveVectors n)
    (hp : p ∈ finiteMixtureFiber A (fittedValueSelection C hCcompact hCnonempty hCpos w))
    (hpfull : ∀ j, 0 < p j)
    (hextreme : p ∈ (finiteMixtureFiber A
      (fittedValueSelection C hCcompact hCnonempty hCpos w)).extremePoints ℝ)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by
  exact finite_extreme_optimizer_jacobian_determinant_lower
    A (fittedValueSelection C hCcompact hCnonempty hCpos w) p w hw hp hpfull
    (hCpos (fittedValueSelection_isMax C hCcompact hCnonempty hCpos w).1)
    (fun j ↦ hCpos (hA (mem_range_self j))) hextreme
    (fittedValueSelection C hCcompact hCnonempty hCpos) hC hA
    (fun q ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q) rfl
    (eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
      C hC hCcompact hCnonempty hCpos w hw) hz a ha0 haUpper

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
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fittedLogSelection C hCcompact hCnonempty hCpos) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^
      (maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal w * fittedLogDerivativeMatrix J).det := by
  classical
  let m := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos) w
  by_cases hm : 0 < m
  · obtain ⟨_, A, hA, hlin, p, hp, hpfull, hpvalue⟩ :=
      maximumIndependentSupport_mem_of_pos D
        (fittedValueSelection C hCcompact hCnonempty hCpos) hm
    have hpFiber : p ∈ finiteMixtureFiber A
        (fittedValueSelection C hCcompact hCnonempty hCpos w) := ⟨hp, hpvalue⟩
    have hsupport : (coefficientSupport p : Set (Fin m)) = univ := by
      ext j
      simp [ne_of_gt (hpfull j)]
    have hlinOn : LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
      rw [hsupport]
      exact linearIndepOn_univ_iff.mpr hlin
    have hext := finiteMixtureFiber_extreme_of_linearIndepOn A _ p hpFiber hlinOn
    letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact canonical_finite_extreme_optimizer_jacobian_determinant_lower
      C hC hCcompact hCnonempty hCpos A (hA.trans hD) p w hw hpFiber hpfull hext hz
        a ha0 haUpper
  · have hmzero : m = 0 := by omega
    have hJ := fittedLogDerivativeMatrix_posSemidef_of_eventually
      (fittedValueSelection C hCcompact hCnonempty hCpos)
      (fun q ↦ fittedValueSelection_isMax C hCcompact hCnonempty hCpos q)
      (fittedOptimalValue (fittedValueSelection C hCcompact hCnonempty hCpos))
      (eventually_canonicalFittedOptimalValue_hasFDerivAt_of_positive_weights
        C hC hCcompact hCnonempty hCpos w hw) hz
    let W : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    have hW : Wᴴ = W := (Matrix.isHermitian_diagonal _).eq
    have hR := hJ.conjTranspose_mul_mul_same W
    rw [hW] at hR
    rw [det_diagonal_add_weight_mul_eq_sqrt_conj w a hw]
    have hd := det_mono_of_posDef_of_sub_posSemidef
      (B := Matrix.diagonal a + W * fittedLogDerivativeMatrix J * W)
      (Matrix.posDef_diagonal_iff.mpr ha0)
      (by simpa using hR)
    change (∏ i, a i) * (17 / 9 : ℝ) ^ (m - 1) ≤ _
    simpa [Matrix.det_diagonal, hmzero, W] using hd
