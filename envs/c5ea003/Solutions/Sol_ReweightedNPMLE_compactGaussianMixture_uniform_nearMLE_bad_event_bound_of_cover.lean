-- Prove2me | solution 1 for ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_bad_event_bound_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:18.796293+00:00
-- url     : https://prove2.me/submissions/57c51c10-897a-4592-a4b7-cf48044c421c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_continuous_gaussianMixture
import Theorems.Thm_ReweightedNPMLE_exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
import Theorems.Thm_ReweightedNPMLE_uniform_nearMLE_hellinger_bad_event_bound

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE





























theorem finiteGaussianMixture_pos {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (x : Point d) :
    0 < finiteGaussianMixture w θ x := by
  have hsumpos : 0 < ∑ i, w i := by rw [hsum]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) ↦ hw i).mp hsumpos
  unfold finiteGaussianMixture
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j) (gaussianKernel_pos d x (θ j)).le
  · exact ⟨i, Finset.mem_univ i, mul_pos hi (gaussianKernel_pos d x (θ i))⟩







/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ

/-- Every translated Gaussian kernel integrates to one. -/
theorem integral_gaussianKernel (d : ℕ) (θ : Point d) :
    ∫ x : Point d, gaussianKernel d x θ = 1 := by
  change (∫ x : Point d, gaussianDensity d (x - θ)) = 1
  rw [integral_sub_right_eq_self, integral_gaussianDensity]

/-- Every finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_integrable {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    Integrable (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture
  exact integrable_finsetSum Finset.univ fun i _ ↦
    (gaussianKernel_integrable d (θ i)).const_mul (w i)

/-- The integral of a finite Gaussian mixture is the sum of its weights. -/
theorem integral_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    ∫ x, finiteGaussianMixture w θ x = ∑ i, w i := by
  unfold finiteGaussianMixture
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_gaussianKernel, mul_one]
  · intro i _
    exact (gaussianKernel_integrable d (θ i)).const_mul (w i)



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasure.
section
/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE









theorem gaussianMixture_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (gaussianMixture μ θ) := by
  exact (gaussianKernel_comp_integrable_prod μ θ hθ).integral_prod_right



theorem measurable_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Measurable (gaussianMixture μ θ) :=
  (continuous_gaussianMixture μ θ hθ).measurable

theorem integral_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    ∫ x : Point d, gaussianMixture μ θ x = 1 := by
  unfold gaussianMixture
  rw [← integral_integral_swap (gaussianKernel_comp_integrable_prod μ θ hθ)]
  simp_rw [integral_gaussianKernel]
  simp



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE





theorem sqrt_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_mul ha]
  ring











/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]



/-- The square-root affinity integrand is integrable for any two integrable
nonnegative densities. -/
theorem sqrt_mul_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ Real.sqrt (p x * q x)) μ := by
  have hhell := hellingerIntegrand_integrable_of_integrable
    μ p q hpmeas hqmeas hp hq hpint hqint
  have hcomb := ((hpint.add hqint).sub hhell).const_mul (1 / 2 : ℝ)
  apply hcomb.congr
  filter_upwards [hp, hq] with x hpx hqx
  have hs := sqrt_sub_sq hpx hqx
  change (1 / 2 : ℝ) *
      (p x + q x - (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) =
    Real.sqrt (p x * q x)
  linarith



































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.SimplexGrid.
section
/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

namespace ReweightedNPMLE





























theorem sum_simplexGridPoint (k M : ℕ) (a : Fin k → Fin (M + 1)) :
    ∑ i, simplexGridPoint k M a i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp [simplexGridPoint]



/-- The simplex grid has at most `(M+1)^k` points. -/
theorem card_simplexWeightGrid_le (k M : ℕ) :
    (simplexWeightGrid k M).card ≤ (M + 1) ^ k := by
  calc
    (simplexWeightGrid k M).card ≤
        (Finset.univ : Finset (Fin k → Fin (M + 1))).card := by
      exact Finset.card_image_le
    _ = (M + 1) ^ k := by simp



theorem mem_validSimplexWeightGrid_iff {k M : ℕ}
    {w : Fin (k + 1) → ℝ} :
    w ∈ validSimplexWeightGrid k M ↔
      w ∈ simplexWeightGrid k M ∧ ∀ i, 0 ≤ w i := by
  simp [validSimplexWeightGrid]

theorem validSimplexWeightGrid_nonneg {k M : ℕ}
    {w : Fin (k + 1) → ℝ} (hw : w ∈ validSimplexWeightGrid k M) (i : Fin (k + 1)) :
    0 ≤ w i :=
  (mem_validSimplexWeightGrid_iff.mp hw).2 i

theorem validSimplexWeightGrid_sum {k M : ℕ}
    {w : Fin (k + 1) → ℝ} (hw : w ∈ validSimplexWeightGrid k M) :
    ∑ i, w i = 1 := by
  rcases (Finset.mem_image.mp
    (mem_validSimplexWeightGrid_iff.mp hw).1) with ⟨a, _, rfl⟩
  exact sum_simplexGridPoint k M a

theorem card_validSimplexWeightGrid_le (k M : ℕ) :
    (validSimplexWeightGrid k M).card ≤ (M + 1) ^ k :=
  (Finset.card_filter_le _ _).trans (card_simplexWeightGrid_le k M)





end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianFiniteNet.
section
/-!
# Finite Gaussian-mixture grids

This module combines a finite location set with the denominator simplex grid.
It produces an actual finite set of Gaussian-mixture densities, proves the
entropy count used in the likelihood-net argument, and packages the local
log-density and global Hellinger rounding estimates for members of that set.
-/

open scoped BigOperators
open MeasureTheory

namespace ReweightedNPMLE





















/-- Cartesian counting gives the explicit entropy bound for the finite
mixture grid. -/
theorem card_finiteGaussianMixtureGrid_le (d k M : ℕ)
    (Q : Finset (Point d)) :
    (finiteGaussianMixtureGrid d k M Q).card ≤
      Q.card ^ (k + 1) * (M + 1) ^ k := by
  classical
  calc
    (finiteGaussianMixtureGrid d k M Q).card ≤
        (((Finset.univ : Finset (Fin (k + 1) → Q)).product
          (validSimplexWeightGrid k M)).card) := by
      exact Finset.card_image_le
    _ = Q.card ^ (k + 1) * (validSimplexWeightGrid k M).card := by
      simp
    _ ≤ Q.card ^ (k + 1) * (M + 1) ^ k :=
      Nat.mul_le_mul_left _ (card_validSimplexWeightGrid_le k M)





theorem mem_finiteGaussianMixtureGrid_iff {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ} :
    p ∈ finiteGaussianMixtureGrid d k M Q ↔
      ∃ (z : Fin (k + 1) → Q) (v : Fin (k + 1) → ℝ),
        v ∈ validSimplexWeightGrid k M ∧
        p = finiteGaussianMixture v (fun i ↦ (z i : Point d)) := by
  classical
  rw [finiteGaussianMixtureGrid, Finset.mem_image]
  constructor
  · rintro ⟨⟨z, v⟩, hzv, rfl⟩
    exact ⟨z, v, (Finset.mem_product.mp hzv).2, rfl⟩
  · rintro ⟨z, v, hv, rfl⟩
    exact ⟨(z, v), Finset.mem_product.mpr ⟨Finset.mem_univ z, hv⟩, rfl⟩

theorem finiteGaussianMixtureGrid_pos {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ}
    (hp : p ∈ finiteGaussianMixtureGrid d k M Q) (x : Point d) :
    0 < p x := by
  rcases (mem_finiteGaussianMixtureGrid_iff Q).mp hp with ⟨z, v, hv, rfl⟩
  exact finiteGaussianMixture_pos _
    (fun i ↦ validSimplexWeightGrid_nonneg hv i)
    (validSimplexWeightGrid_sum hv) x

theorem finiteGaussianMixtureGrid_integrable {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ}
    (hp : p ∈ finiteGaussianMixtureGrid d k M Q) :
    Integrable p := by
  rcases (mem_finiteGaussianMixtureGrid_iff Q).mp hp with ⟨z, v, _hv, rfl⟩
  exact finiteGaussianMixture_integrable v (fun i ↦ (z i : Point d))

theorem integral_finiteGaussianMixtureGrid {d k M : ℕ}
    (Q : Finset (Point d)) {p : Point d → ℝ}
    (hp : p ∈ finiteGaussianMixtureGrid d k M Q) :
    ∫ x, p x = 1 := by
  rcases (mem_finiteGaussianMixtureGrid_iff Q).mp hp with ⟨z, v, hv, rfl⟩
  rw [integral_finiteGaussianMixture]
  exact validSimplexWeightGrid_sum hv













end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianNearMLE.
section
/-!
# Uniform near-MLE control for compact Gaussian mixtures

This module closes the main interface between the analytic Gaussian-mixture
net and the finite likelihood-ratio test.  Candidates are genuine bundled
probability measures on a compact location set, rather than a finite-mixture
surrogate parameterization.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace ReweightedNPMLE



theorem compactGaussianMixtureDensity_measurable {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    Measurable (compactGaussianMixtureDensity G) := by
  exact measurable_gaussianMixture (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe

theorem compactGaussianMixtureDensity_pos {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) (x : Point d) :
    0 < compactGaussianMixtureDensity G x := by
  exact gaussianMixture_pos (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe x

theorem compactGaussianMixtureDensity_integrable {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    Integrable (compactGaussianMixtureDensity G) := by
  exact gaussianMixture_integrable (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe

theorem integral_compactGaussianMixtureDensity {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    ∫ x, compactGaussianMixtureDensity G x = 1 := by
  exact integral_gaussianMixture (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe

























end ReweightedNPMLE
end

/-!
# Uniform near-MLE control for compact Gaussian mixtures

This module closes the main interface between the analytic Gaussian-mixture
net and the finite likelihood-ratio test.  Candidates are genuine bundled
probability measures on a compact location set, rather than a finite-mixture
surrogate parameterization.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Uniform likelihood/Hellinger control for every near-MLE over all mixing
laws supported on a compact location set, using any supplied finite internal
location cover. -/
theorem solution
    {d L M n : ℕ}
    (K X : Set (Point d)) (Q : Finset (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hQK : ↑Q ⊆ K)
    (hQcover : ∀ u ∈ K, ∃ v ∈ Q, ‖u - v‖ ≤ ε)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2)
    (Gstar : ProbabilityMeasure K) (t radiusBound : ℝ)
    (hnδ : (n : ℝ) * gaussianNetLogError d L M T S ε ≤ 1)
    (hradius :
      (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
        ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
          ({x : Fin n → Point d | ∀ i, x i ∈ X}ᶜ) ≤ radiusBound) :
    (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
      ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
        {x | ∃ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
          2 * gaussianNetHellingerSqError d L M S ε + 2 * t ^ 2 <
            hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar)} ≤
      radiusBound +
        (Q.card ^ (gaussianMomentDimension d L + 1) * (M + 1) ^
              gaussianMomentDimension d L) *
          Real.exp (1 - (n : ℝ) * t ^ 2 / 2) := by
  classical
  let k := gaussianMomentDimension d L
  let N := finiteGaussianMixtureGrid d k M Q
  let f : ProbabilityMeasure K → Point d → ℝ :=
    fun G ↦ compactGaussianMixtureDensity G
  let q : Point d → ℝ := compactGaussianMixtureDensity Gstar
  let δ := gaussianNetLogError d L M T S ε
  let globalSq := gaussianNetHellingerSqError d L M S ε
  have happ : ∀ G : ProbabilityMeasure K, ∃ p ∈ N,
      hellingerSq volume (f G) p ≤ globalSq ∧
      ∀ x ∈ X, |Real.log (p x) - Real.log (f G x)| ≤ δ := by
    intro G
    simpa only [N, k, f, δ, globalSq,
      compactGaussianMixtureDensity, gaussianNetHellingerSqError,
      gaussianNetLogError] using
      (exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
        (G : Measure K) (fun θ : K ↦ (θ : Point d))
        measurable_subtype_coe K X Q hKcompact hKnonempty
        (fun θ : K ↦ θ.property) hT hS hε hKbound hXbound hQK hQcover hM
        hrelativeHalf hweightSmall)
  let select : ProbabilityMeasure K → (Point d → ℝ) :=
    fun G ↦ (happ G).choose
  have hselect : ∀ G, select G ∈ N := fun G ↦ (happ G).choose_spec.1
  have hglobal : ∀ G,
      hellingerSq volume (f G) (select G) ≤ globalSq :=
    fun G ↦ (happ G).choose_spec.2.1
  have hlocal : ∀ G x, x ∈ X →
      |Real.log (select G x) - Real.log (f G x)| ≤ δ :=
    fun G ↦ (happ G).choose_spec.2.2
  have hqmeas : Measurable q := compactGaussianMixtureDensity_measurable Gstar
  have hq : ∀ x, 0 < q x := compactGaussianMixtureDensity_pos Gstar
  have hqint : Integrable q := compactGaussianMixtureDensity_integrable Gstar
  have hqone : ∫ x, q x = 1 := integral_compactGaussianMixtureDensity Gstar
  have hmain := uniform_nearMLE_hellinger_bad_event_bound
    volume N (fun p : Point d → ℝ ↦ p) q f select
    {x : Fin n → Point d | ∀ i, x i ∈ X} δ globalSq t radiusBound
    hqmeas hq hqint hqone
    (fun p hp ↦ finiteGaussianMixtureGrid_pos Q hp)
    (fun p hp ↦ finiteGaussianMixtureGrid_integrable Q hp)
    (fun p hp ↦ sqrt_mul_integrable_of_integrable volume p q
      (finiteGaussianMixtureGrid_integrable Q hp).aestronglyMeasurable
      hqint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x ↦
        (finiteGaussianMixtureGrid_pos Q hp x).le)
      (Filter.Eventually.of_forall fun x ↦ (hq x).le)
      (finiteGaussianMixtureGrid_integrable Q hp) hqint)
    (fun p hp ↦ integral_finiteGaussianMixtureGrid Q hp)
    (fun G ↦ compactGaussianMixtureDensity_pos G)
    (fun G ↦ compactGaussianMixtureDensity_integrable G)
    hselect hglobal
    (fun x hx G i ↦ hlocal G (x i) (hx i)) hnδ hradius
  have hcardNat : N.card ≤ Q.card ^ (k + 1) * (M + 1) ^ k := by
    exact card_finiteGaussianMixtureGrid_le d k M Q
  have hcard : (N.card : ℝ) ≤
      (Q.card : ℝ) ^ (k + 1) * ((M : ℝ) + 1) ^ k := by
    exact_mod_cast hcardNat
  have hmul : (N.card : ℝ) * Real.exp (1 - (n : ℝ) * t ^ 2 / 2) ≤
      (Q.card : ℝ) ^ (k + 1) * ((M : ℝ) + 1) ^ k *
        Real.exp (1 - (n : ℝ) * t ^ 2 / 2) :=
    mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
  exact hmain.trans (by
    simpa only [N, k, f, q, δ, globalSq] using
      add_le_add (le_refl radiusBound) hmul)
