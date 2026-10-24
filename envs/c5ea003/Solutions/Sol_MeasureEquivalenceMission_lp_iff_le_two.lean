-- Prove2me | solution 1 for MeasureEquivalenceMission.lp_iff_le_two
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-24T02:51:40.328341+00:00
-- url     : https://prove2.me/submissions/8865d192-f22e-44f8-b28c-1274c1498f9f

import Definitions.Def_MeasureEquivalenceSequences
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Topology.Algebra.MulAction
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Action
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Topology.Maps.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Constructions

/- Source module: GaussianFinite -/
section MainProofScope0
/-! Concrete variance-one Gaussian likelihood and affinity identities.
This file does not claim the infinite Gaussian product criterion.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace MeasureEquivalenceGaussian

noncomputable def likelihood (a b x : ℝ) : ℝ :=
  Real.exp ((a - b) * x + (-(a ^ 2 - b ^ 2) / 2))

noncomputable def rootLikelihood (a b x : ℝ) : ℝ :=
  Real.exp (((a - b) / 2) * x + (-(a ^ 2 - b ^ 2) / 4))

lemma rootLikelihood_sq (a b x : ℝ) :
    rootLikelihood a b x ^ 2 = likelihood a b x := by
  simp only [rootLikelihood, likelihood, pow_two, ← Real.exp_add]
  congr 1
  ring

lemma integral_exp_affine (b t c : ℝ) :
    (∫ x, Real.exp (t * x + c) ∂gaussianReal b 1) =
      Real.exp (b * t + t ^ 2 / 2 + c) := by
  have hm : (∫ x, Real.exp (t * x) ∂gaussianReal b 1) =
      Real.exp (b * t + t ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := b) (v := 1)) t
  simp_rw [Real.exp_add]
  rw [integral_mul_const, hm]
  simp [Real.exp_add]

lemma integrable_exp_affine (b t c : ℝ) :
    Integrable (fun x => Real.exp (t * x + c)) (gaussianReal b 1) := by
  simp_rw [Real.exp_add]
  exact (integrable_exp_mul_gaussianReal (μ := b) (v := 1) t).mul_const _

theorem integral_likelihood (a b : ℝ) :
    (∫ x, likelihood a b x ∂gaussianReal b 1) = 1 := by
  simp only [likelihood]
  rw [integral_exp_affine]
  have h : b * (a - b) + (a - b) ^ 2 / 2 + -(a ^ 2 - b ^ 2) / 2 = 0 := by ring
  rw [h, Real.exp_zero]

theorem integral_rootLikelihood (a b : ℝ) :
    (∫ x, rootLikelihood a b x ∂gaussianReal b 1) =
      Real.exp (-(a - b) ^ 2 / 8) := by
  simp only [rootLikelihood]
  rw [integral_exp_affine]
  congr 1
  ring

lemma integrable_likelihood (a b : ℝ) :
    Integrable (likelihood a b) (gaussianReal b 1) :=
  integrable_exp_affine b (a - b) (-(a ^ 2 - b ^ 2) / 2)

lemma integrable_rootLikelihood (a b : ℝ) :
    Integrable (rootLikelihood a b) (gaussianReal b 1) :=
  integrable_exp_affine b ((a - b) / 2) (-(a ^ 2 - b ^ 2) / 4)

theorem gaussian_withDensity_likelihood (a b : ℝ) :
    (gaussianReal b 1).withDensity (fun x => ENNReal.ofReal (likelihood a b x)) =
      gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero b one_ne_zero,
    gaussianReal_of_var_ne_zero a one_ne_zero]
  rw [← withDensity_mul volume (measurable_gaussianPDF b 1)
    (show Measurable (fun x => ENNReal.ofReal (likelihood a b x)) by
      unfold likelihood
      fun_prop)]
  apply withDensity_congr_ae
  apply ae_of_all
  intro x
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg b 1 x)]
  congr 1
  simp only [gaussianPDFReal, likelihood, NNReal.coe_one, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

lemma gaussian_set_likelihood (a b : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ x in s, likelihood a b x ∂gaussianReal b 1) =
      gaussianReal a 1 s := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_likelihood a b).restrict
    (ae_of_all _ (fun x => (Real.exp_pos _).le))]
  rw [← withDensity_apply _ hs, gaussian_withDensity_likelihood]

theorem finite_gaussian_withDensity_likelihood
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (Measure.pi (fun i => gaussianReal (b i) 1)).withDensity
        (fun x => ENNReal.ofReal (∏ i, likelihood (a i) (b i) (x i))) =
      Measure.pi (fun i => gaussianReal (a i) 1) := by
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal
      (Integrable.fintype_prod (fun i => integrable_likelihood (a i) (b i))).restrict
      (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hnonneg (i : ι) : 0 ≤ ∫ x in s i, likelihood (a i) (b i) x
      ∂gaussianReal (b i) 1 := integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hnonneg i)]
  apply Finset.prod_congr rfl
  intro i _
  exact gaussian_set_likelihood (a i) (b i) (hs i)

theorem finite_gaussian_affinity {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∫ x : ι → ℝ, ∏ i, rootLikelihood (a i) (b i) (x i)
      ∂Measure.pi (fun i => gaussianReal (b i) 1)) =
      Real.exp (-(∑ i, (a i - b i) ^ 2) / 8) := by
  rw [integral_fintype_prod_eq_prod]
  simp_rw [integral_rootLikelihood]
  rw [← Real.exp_sum]
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem finite_gaussian_second_moment {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∫ x : ι → ℝ, (∏ i, rootLikelihood (a i) (b i) (x i)) ^ 2
      ∂Measure.pi (fun i => gaussianReal (b i) 1)) = 1 := by
  simp_rw [← Finset.prod_pow, rootLikelihood_sq]
  rw [integral_fintype_prod_eq_prod]
  simp [integral_likelihood]

noncomputable def gaussianProduct (a : ℕ → ℝ) : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun n => gaussianReal (a n) 1)

noncomputable def blockRoot (I : Finset ℕ) (a b : ℕ → ℝ) (x : ℕ → ℝ) : ℝ :=
  ∏ i : I, rootLikelihood (a i) (b i) (x i)

theorem gaussian_product_block_affinity (I : Finset ℕ) (a b : ℕ → ℝ) :
    (∫ x, blockRoot I a b x ∂gaussianProduct b) =
      Real.exp (-(∑ i : I, (a i - b i) ^ 2) / 8) := by
  change (∫ x, (fun y : I → ℝ => ∏ i : I, rootLikelihood (a i) (b i) (y i))
    (I.restrict x) ∂Measure.infinitePi (fun n => gaussianReal (b n) 1)) = _
  rw [integral_restrict_infinitePi (fun n => gaussianReal (b n) 1)
    (s := I) (f := fun y : I → ℝ => ∏ i : I, rootLikelihood (a i) (b i) (y i)) (by
    apply Continuous.aestronglyMeasurable
    unfold rootLikelihood
    fun_prop)]
  exact finite_gaussian_affinity (fun i : I => a i) (fun i : I => b i)

theorem gaussian_product_block_second_moment (I : Finset ℕ) (a b : ℕ → ℝ) :
    (∫ x, blockRoot I a b x ^ 2 ∂gaussianProduct b) = 1 := by
  change (∫ x, (fun y : I → ℝ => (∏ i : I, rootLikelihood (a i) (b i) (y i)) ^ 2)
    (I.restrict x) ∂Measure.infinitePi (fun n => gaussianReal (b n) 1)) = _
  rw [integral_restrict_infinitePi (fun n => gaussianReal (b n) 1)
    (s := I) (f := fun y : I → ℝ => (∏ i : I, rootLikelihood (a i) (b i) (y i)) ^ 2) (by
    apply Continuous.aestronglyMeasurable
    unfold rootLikelihood
    fun_prop)]
  exact finite_gaussian_second_moment (fun i : I => a i) (fun i : I => b i)

theorem gaussian_product_block_memLp (I : Finset ℕ) (a b : ℕ → ℝ) :
    MemLp (blockRoot I a b) 2 (gaussianProduct b) := by
  apply (memLp_two_iff_integrable_sq (by
    apply Continuous.aestronglyMeasurable
    unfold blockRoot rootLikelihood
    fun_prop)).mpr
  apply Integrable.of_integral_ne_zero
  rw [gaussian_product_block_second_moment]
  exact one_ne_zero

end MeasureEquivalenceGaussian
end MainProofScope0

/- Source module: DensitySquare -/
section MainProofScope1
/-! The concrete L2-to-L1 density-square estimate used in the written proof.
This does not define a Hellinger distance or a topology on probability measures.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

noncomputable def square (f : Lp ℝ 2 μ) : Lp ℝ 1 μ := f • f

lemma square_coe (f : Lp ℝ 2 μ) :
    square μ f =ᵐ[μ] fun x => f x ^ 2 := by
  filter_upwards [Lp.coeFn_lpSMul f f (r := 1)] with x hx
  simpa [square, sq, smul_eq_mul] using hx

lemma square_sub_factor (f g : Lp ℝ 2 μ) :
    square μ f - square μ g = ((f - g) • (f + g) : Lp ℝ 1 μ) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (square μ f) (square μ g),
    square_coe μ f, square_coe μ g,
    Lp.coeFn_lpSMul (f - g) (f + g) (r := 1),
    Lp.coeFn_sub f g, Lp.coeFn_add f g] with x hs hf hg hm hd ha
  simp only [Pi.sub_apply, Pi.add_apply, smul_eq_mul, Pi.mul_apply] at *
  rw [hs, hf, hg, hm, hd, ha]
  ring

theorem square_difference_bound (f g : Lp ℝ 2 μ) :
    ‖square μ f - square μ g‖ ≤ ‖f - g‖ * (‖f‖ + ‖g‖) := by
  rw [square_sub_factor]
  exact (Lp.norm_smul_le (r := 1) (f - g) (f + g)).trans
    (mul_le_mul_of_nonneg_left (norm_add_le f g) (norm_nonneg _))

theorem square_continuous : Continuous (square μ) := by
  have h : square μ = fun f : Lp ℝ 2 μ =>
      (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 f f := by
    funext f
    apply Lp.ext
    filter_upwards [square_coe μ f,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) f f] with x h1 h2
    change (square μ f) x =
      ((ContinuousLinearMap.mul ℝ ℝ).holder 1 f f) x
    rw [h1, h2]
    simp [pow_two]
  rw [h]
  exact (ContinuousLinearMap.mul ℝ ℝ).holderL μ 2 2 1 |>.continuous.clm_apply continuous_id

theorem square_injective_on_nonnegative :
    Set.InjOn (square μ) (Set.Ici (0 : Lp ℝ 2 μ)) := by
  intro f hf g hg hfg
  apply Lp.ext
  have heq : square μ f =ᵐ[μ] square μ g :=
    Filter.Eventually.of_forall (fun x => congrArg (fun h : Lp ℝ 1 μ => h x) hfg)
  filter_upwards [square_coe μ f, square_coe μ g, heq,
    (Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x h1 h2 h3 h4 h5
  have hs : f x ^ 2 = g x ^ 2 := h1.symm.trans (h3.trans h2)
  change 0 ≤ f x at h4
  change 0 ≤ g x at h5
  nlinarith

def positiveUnitSphere : Set (Lp ℝ 2 μ) := {f | 0 ≤ f ∧ ‖f‖ = 1}

theorem positiveUnitSphere_closed : IsClosed (positiveUnitSphere μ) := by
  change IsClosed ({f : Lp ℝ 2 μ | 0 ≤ f} ∩ {f : Lp ℝ 2 μ | ‖f‖ = 1})
  exact (isClosed_le continuous_const continuous_id).inter
    (isClosed_eq continuous_norm continuous_const)

theorem positiveUnitSphere_complete : CompleteSpace (positiveUnitSphere μ) :=
  (positiveUnitSphere_closed μ).isComplete.completeSpace_coe

end MeasureEquivalenceDensity
end MainProofScope1

/- Source module: DensityExtension -/
section MainProofScope2
/-!
Actual measure identification from nonnegative L1 density approximations.
The hypotheses concern a generating pi-system; the conclusion is equality
of measures, followed by absolute continuity. No Gaussian identities or
product-affinity computations are assumed to have been formalized here.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureEquivalenceDensityExtension

variable {α : Type*} [m : MeasurableSpace α]
  {μ ν : Measure α} [IsFiniteMeasure ν]

theorem measure_eq_withDensity_of_L1_approx
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hpos : ∀ n, 0 ≤ f n)
    (hlim : Tendsto f atTop (𝓝 g))
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, f n x ∂μ) = ν s) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
  have hgpos : g ∈ Set.Ici (0 : Lp ℝ 1 μ) :=
    isClosed_Ici.mem_of_tendsto hlim (Eventually.of_forall hpos)
  have hg_ae : 0 ≤ᵐ[μ] g := (Lp.coeFn_nonneg g).mpr hgpos
  have hvals : ∀ s ∈ C,
      ENNReal.ofReal (∫ x in s, g x ∂μ) = ν s := by
    intro s hs
    apply tendsto_nhds_unique
      ((ENNReal.continuous_ofReal.comp (continuous_setIntegral s)).tendsto g |>.comp hlim)
    exact tendsto_const_nhds.congr' (by
      filter_upwards [hmatch s hs] with n hn
      exact hn.symm)
  have hmeas : ∀ s ∈ C, MeasurableSet s := by
    intro s hs
    rw [hgen]
    exact MeasurableSpace.measurableSet_generateFrom hs
  have hwd : ∀ s ∈ C,
      μ.withDensity (fun x => ENNReal.ofReal (g x)) s = ν s := by
    intro s hs
    rw [withDensity_apply _ (hmeas s hs),
      ← ofReal_integral_eq_lintegral_ofReal
        (L1.integrable_coeFn g).restrict (ae_restrict_of_ae hg_ae)]
    exact hvals s hs
  exact ext_of_generate_finite C hgen hpi
    (fun s hs => (hwd s hs).symm) (hwd Set.univ huniv).symm

theorem absolutelyContinuous_of_L1_approx
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hpos : ∀ n, 0 ≤ f n)
    (hlim : Tendsto f atTop (𝓝 g))
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, f n x ∂μ) = ν s) :
    ν ≪ μ := by
  rw [measure_eq_withDensity_of_L1_approx C hgen hpi huniv f g hpos hlim hmatch]
  exact withDensity_absolutelyContinuous _ _

theorem product_measure_eq_withDensity_of_L1_cylinder_approx
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ ν : Measure (∀ i, X i)} [IsFiniteMeasure ν]
    (f : ℕ → Lp ℝ 1 μ) (g : Lp ℝ 1 μ)
    (hpos : ∀ n, 0 ≤ f n)
    (hlim : Tendsto f atTop (𝓝 g))
    (hmatch : ∀ (I : Finset ι) (s : Set (∀ i : I, X i)), MeasurableSet s →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (∫ x in cylinder I s, f n x ∂μ) = ν (cylinder I s)) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) := by
  apply measure_eq_withDensity_of_L1_approx (measurableCylinders X)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders X) f g hpos hlim
  intro s hs
  obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  exact hmatch I t ht

end MeasureEquivalenceDensityExtension
end MainProofScope2

/- Source module: ProductAffinity -/
section MainProofScope3
/-! A positive affinity criterion with actual measures and L2 functions.
Unit-norm L2 approximations whose pairwise affinities tend to one are
Cauchy. If their squared densities match the target measure eventually
on a generating pi-system, the target is absolutely continuous.
No Gaussian instantiation or singular alternative is claimed here.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace MeasureEquivalenceProductAffinity

theorem cauchySeq_of_unit_inner_tendsto_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ℕ → E) (hunit : ∀ n, ‖u n‖ = 1)
    (haff : Tendsto (fun p : ℕ × ℕ => ⟪u p.1, u p.2⟫_ℝ) atTop (𝓝 1)) :
    CauchySeq u := by
  have hdist (p : ℕ × ℕ) :
      dist (u p.1) (u p.2) = Real.sqrt (2 - 2 * ⟪u p.1, u p.2⟫_ℝ) := by
    have hs : ‖u p.1 - u p.2‖ ^ 2 = 2 - 2 * ⟪u p.1, u p.2⟫_ℝ := by
      rw [norm_sub_sq_real, hunit, hunit]
      ring
    rw [← hs, Real.sqrt_sq (norm_nonneg _), dist_eq_norm]
  have hsq : Tendsto (fun p : ℕ × ℕ => 2 - 2 * ⟪u p.1, u p.2⟫_ℝ)
      atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_nhds.sub (haff.const_mul 2)) using 1
    norm_num
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have ht' := ht.congr' (Eventually.of_forall (fun p => (hdist p).symm))
  simpa only [Real.sqrt_zero] using ht'

variable {α : Type*} [m : MeasurableSpace α]
  {μ ν : Measure α} [IsFiniteMeasure ν]

theorem absolutelyContinuous_of_L2_cauchy_cylinder_densities
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (u : ℕ → Lp ℝ 2 μ) (hcauchy : CauchySeq u)
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, (u n x) ^ 2 ∂μ) = ν s) :
    ν ≪ μ := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  let f : ℕ → Lp ℝ 1 μ := fun n => MeasureEquivalenceDensity.square μ (u n)
  have hpos : ∀ n, 0 ≤ f n := by
    intro n
    apply (Lp.coeFn_nonneg (f n)).mp
    filter_upwards [MeasureEquivalenceDensity.square_coe μ (u n)] with x hx
    change 0 ≤ (MeasureEquivalenceDensity.square μ (u n)) x
    rw [hx]
    exact sq_nonneg _
  apply MeasureEquivalenceDensityExtension.absolutelyContinuous_of_L1_approx
    C hgen hpi huniv f (MeasureEquivalenceDensity.square μ g) hpos
    ((MeasureEquivalenceDensity.square_continuous μ).tendsto g |>.comp hg)
  intro s hs
  filter_upwards [hmatch s hs] with n hn
  have hi : (∫ x in s, f n x ∂μ) = ∫ x in s, (u n x) ^ 2 ∂μ :=
    integral_congr_ae (ae_restrict_of_ae (MeasureEquivalenceDensity.square_coe μ (u n)))
  rw [hi]
  exact hn

theorem absolutelyContinuous_of_affinity_tendsto_one
    (C : Set (Set α)) (hgen : m = MeasurableSpace.generateFrom C)
    (hpi : IsPiSystem C) (huniv : Set.univ ∈ C)
    (u : ℕ → Lp ℝ 2 μ) (hunit : ∀ n, ‖u n‖ = 1)
    (haff : Tendsto (fun p : ℕ × ℕ => ⟪u p.1, u p.2⟫_ℝ) atTop (𝓝 1))
    (hmatch : ∀ s ∈ C, ∀ᶠ n in atTop,
      ENNReal.ofReal (∫ x in s, (u n x) ^ 2 ∂μ) = ν s) :
    ν ≪ μ :=
  absolutelyContinuous_of_L2_cauchy_cylinder_densities C hgen hpi huniv u
    (cauchySeq_of_unit_inner_tendsto_one u hunit haff) hmatch

theorem product_absolutelyContinuous_of_affinity_tendsto_one
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    {μ ν : Measure (∀ i, X i)} [IsFiniteMeasure ν]
    (u : ℕ → Lp ℝ 2 μ) (hunit : ∀ n, ‖u n‖ = 1)
    (haff : Tendsto (fun p : ℕ × ℕ => ⟪u p.1, u p.2⟫_ℝ) atTop (𝓝 1))
    (hmatch : ∀ (I : Finset ι) (s : Set (∀ i : I, X i)), MeasurableSet s →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (∫ x in cylinder I s, (u n x) ^ 2 ∂μ) = ν (cylinder I s)) :
    ν ≪ μ := by
  apply absolutelyContinuous_of_affinity_tendsto_one (measurableCylinders X)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    (univ_mem_measurableCylinders X) u hunit haff
  intro s hs
  obtain ⟨I, t, ht, rfl⟩ := (mem_measurableCylinders s).mp hs
  exact hmatch I t ht

theorem mutuallySingular_of_summable_tests
    {μ ν : Measure α} (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n))
    (hμ : (∑' n, μ (A n)) ≠ ∞) (hν : (∑' n, ν (A n)ᶜ) ≠ ∞) :
    μ ⟂ₘ ν := by
  refine ⟨Filter.liminf A atTop, MeasurableSet.measurableSet_liminf hA,
    measure_liminf_atTop_eq_zero hμ, ?_⟩
  rw [Filter.liminf_compl]
  exact measure_limsup_atTop_eq_zero hν

end MeasureEquivalenceProductAffinity
end MainProofScope3

/- Source module: GaussianCriterion -/
section MainProofScope4
/-! Assembly of the infinite Gaussian product criterion.
Only completed lemmas are included; no placeholder assumptions are used.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal BigOperators Topology InnerProductSpace

namespace MeasureEquivalenceGaussian

instance gaussianProduct_probability (a : ℕ → ℝ) : IsProbabilityMeasure (gaussianProduct a) := by
  unfold gaussianProduct
  infer_instance

lemma continuous_blockRoot (I : Finset ℕ) (a b : ℕ → ℝ) :
    Continuous (blockRoot I a b) := by
  unfold blockRoot rootLikelihood
  fun_prop

lemma blockRoot_nonneg (I : Finset ℕ) (a b : ℕ → ℝ) (x : ℕ → ℝ) :
    0 ≤ blockRoot I a b x :=
  Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le)

lemma map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : β → ℝ≥0∞} {g : α → β}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (fun x => f (g x))).map g = (μ.map g).withDensity f := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs),
    withDensity_apply _ hs, setLIntegral_map hs hf hg]

lemma weighted_block_map (I : Finset ℕ) (a b : ℕ → ℝ) :
    ((gaussianProduct b).withDensity (fun x => ENNReal.ofReal (blockRoot I a b x ^ 2))).map
      I.restrict = Measure.pi (fun i : I => gaussianReal (a i) 1) := by
  have heq : (fun x => ENNReal.ofReal (blockRoot I a b x ^ 2)) =
      (fun x => (fun y : I → ℝ => ENNReal.ofReal
        (∏ i : I, likelihood (a i) (b i) (y i))) (I.restrict x)) := by
    funext x
    simp only [blockRoot, ← Finset.prod_pow, rootLikelihood_sq]
    rfl
  rw [heq]
  rw [map_withDensity_comp (gaussianProduct b)
    (f := fun y : I → ℝ => ENNReal.ofReal (∏ i : I, likelihood (a i) (b i) (y i)))
    (g := I.restrict) (by unfold likelihood; fun_prop) (Finset.measurable_restrict I)]
  change ((Measure.infinitePi (fun n => gaussianReal (b n) 1)).map I.restrict).withDensity _ = _
  rw [Measure.infinitePi_map_restrict, finite_gaussian_withDensity_likelihood]

lemma weighted_block_map_subset {I J : Finset ℕ} (hJI : J ⊆ I) (a b : ℕ → ℝ) :
    ((gaussianProduct b).withDensity (fun x => ENNReal.ofReal (blockRoot I a b x ^ 2))).map
      J.restrict = Measure.pi (fun j : J => gaussianReal (a j) 1) := by
  have hm := congrArg
    (fun η : Measure (I → ℝ) => η.map (Finset.restrict₂ (π := fun _ : ℕ => ℝ) hJI))
    (weighted_block_map I a b)
  dsimp only at hm
  rw [Measure.map_map (Finset.measurable_restrict₂ hJI) (Finset.measurable_restrict I),
    Finset.restrict₂_comp_restrict] at hm
  exact hm.trans (isProjectiveMeasureFamily_pi (fun n => gaussianReal (a n) 1) I J hJI).symm

lemma block_cylinder_density {I J : Finset ℕ} (hJI : J ⊆ I) (a b : ℕ → ℝ)
    {s : Set (J → ℝ)} (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ x in cylinder J s, blockRoot I a b x ^ 2 ∂gaussianProduct b) =
      gaussianProduct a (cylinder J s) := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (gaussian_product_block_memLp I a b).integrable_sq.restrict
    (ae_of_all _ (fun x => sq_nonneg _))]
  change (∫⁻ x in J.restrict ⁻¹' s, ENNReal.ofReal (blockRoot I a b x ^ 2)
    ∂gaussianProduct b) = _
  rw [← withDensity_apply _ (Finset.measurable_restrict J hs)]
  change ((gaussianProduct b).withDensity _ ) (J.restrict ⁻¹' s) = _
  rw [← Measure.map_apply (Finset.measurable_restrict J) hs, weighted_block_map_subset hJI]
  exact (Measure.infinitePi_cylinder (fun n => gaussianReal (a n) 1) hs).symm

noncomputable def blockRootLp (I : Finset ℕ) (a b : ℕ → ℝ) : Lp ℝ 2 (gaussianProduct b) :=
  (gaussian_product_block_memLp I a b).toLp (blockRoot I a b)

lemma blockRootLp_coe (I : Finset ℕ) (a b : ℕ → ℝ) :
    blockRootLp I a b =ᵐ[gaussianProduct b] blockRoot I a b :=
  MemLp.coeFn_toLp (gaussian_product_block_memLp I a b)

lemma blockRootLp_unit (I : Finset ℕ) (a b : ℕ → ℝ) : ‖blockRootLp I a b‖ = 1 := by
  have hi : ⟪blockRootLp I a b, blockRootLp I a b⟫_ℝ = 1 := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, blockRoot I a b x ^ 2 ∂gaussianProduct b := by
        apply integral_congr_ae
        filter_upwards [blockRootLp_coe I a b] with x hx
        simp [hx, pow_two]
      _ = 1 := gaussian_product_block_second_moment I a b
  rw [real_inner_self_eq_norm_sq] at hi
  nlinarith [norm_nonneg (blockRootLp I a b)]

lemma blockRoot_sdiff {I J : Finset ℕ} (hIJ : I ⊆ J) (a b : ℕ → ℝ) (x : ℕ → ℝ) :
    blockRoot J a b x = blockRoot (J \ I) a b x * blockRoot I a b x := by
  unfold blockRoot
  rw [Finset.prod_coe_sort J (fun i : ℕ => rootLikelihood (a i) (b i) (x i)),
    Finset.prod_coe_sort (J \ I) (fun i : ℕ => rootLikelihood (a i) (b i) (x i)),
    Finset.prod_coe_sort I (fun i : ℕ => rootLikelihood (a i) (b i) (x i))]
  exact (Finset.prod_sdiff hIJ).symm

lemma blockRoot_indep (I J : Finset ℕ) (hIJ : Disjoint I J) (a b : ℕ → ℝ) :
    IndepFun (fun x => blockRoot I a b x ^ 2) (blockRoot J a b) (gaussianProduct b) := by
  have hind : iIndepFun (fun n (x : ℕ → ℝ) => x n) (gaussianProduct b) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hb := hind.indepFun_finset I J hIJ (fun _ => measurable_pi_apply _)
  exact hb.comp
    (show Measurable (fun y : I → ℝ => (∏ i : I, rootLikelihood (a i) (b i) (y i)) ^ 2) by
      unfold rootLikelihood
      fun_prop)
    (show Measurable (fun y : J → ℝ => ∏ i : J, rootLikelihood (a i) (b i) (y i)) by
      unfold rootLikelihood
      fun_prop)

lemma blockRootLp_inner_of_subset {I J : Finset ℕ} (hIJ : I ⊆ J) (a b : ℕ → ℝ) :
    ⟪blockRootLp I a b, blockRootLp J a b⟫_ℝ =
      Real.exp (-(∑ i ∈ J \ I, (a i - b i) ^ 2) / 8) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, blockRoot I a b x ^ 2 * blockRoot (J \ I) a b x ∂gaussianProduct b := by
      apply integral_congr_ae
      filter_upwards [blockRootLp_coe I a b, blockRootLp_coe J a b] with x hi hj
      simp only [hi, hj, Real.inner_apply]
      rw [blockRoot_sdiff hIJ]
      ring
    _ = (∫ x, blockRoot I a b x ^ 2 ∂gaussianProduct b) *
        ∫ x, blockRoot (J \ I) a b x ∂gaussianProduct b := by
      exact (blockRoot_indep I (J \ I) disjoint_sdiff_self_right a b).integral_fun_mul_eq_mul_integral
        (continuous_blockRoot I a b |>.pow 2 |>.aestronglyMeasurable)
        (continuous_blockRoot (J \ I) a b).aestronglyMeasurable
    _ = _ := by
      rw [gaussian_product_block_second_moment, gaussian_product_block_affinity, one_mul]
      rw [Finset.sum_coe_sort (J \ I) (fun i : ℕ => (a i - b i) ^ 2)]

noncomputable def energy (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, (a i - b i) ^ 2

lemma energy_mono (a b : ℕ → ℝ) : Monotone (energy a b) := by
  intro m n hmn
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun _ _ _ => sq_nonneg _)

lemma range_inner_of_le (a b : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ⟪blockRootLp (Finset.range m) a b, blockRootLp (Finset.range n) a b⟫_ℝ =
      Real.exp (-|energy a b n - energy a b m| / 8) := by
  rw [blockRootLp_inner_of_subset (Finset.range_mono hmn),
    Finset.sum_sdiff_eq_sub (Finset.range_mono hmn),
    abs_of_nonneg (sub_nonneg.mpr (energy_mono a b hmn))]
  rfl

lemma range_inner (a b : ℕ → ℝ) (m n : ℕ) :
    ⟪blockRootLp (Finset.range m) a b, blockRootLp (Finset.range n) a b⟫_ℝ =
      Real.exp (-|energy a b n - energy a b m| / 8) := by
  obtain h | h := le_total m n
  · exact range_inner_of_le a b h
  · rw [real_inner_comm, range_inner_of_le a b h, abs_sub_comm]

lemma range_affinity_tendsto_one (a b : ℕ → ℝ)
    (hs : Summable (fun n => (a n - b n) ^ 2)) :
    Tendsto (fun p : ℕ × ℕ =>
      ⟪blockRootLp (Finset.range p.1) a b, blockRootLp (Finset.range p.2) a b⟫_ℝ)
      atTop (𝓝 1) := by
  have hE : Tendsto (energy a b) atTop (𝓝 (∑' n, (a n - b n) ^ 2)) :=
    hs.hasSum.tendsto_sum_nat
  have hf : Tendsto (fun p : ℕ × ℕ => energy a b p.1) atTop
      (𝓝 (∑' n, (a n - b n) ^ 2)) := by
    rw [← prod_atTop_atTop_eq]
    exact hE.comp tendsto_fst
  have hg : Tendsto (fun p : ℕ × ℕ => energy a b p.2) atTop
      (𝓝 (∑' n, (a n - b n) ^ 2)) := by
    rw [← prod_atTop_atTop_eq]
    exact hE.comp tendsto_snd
  have hd : Tendsto (fun p : ℕ × ℕ => energy a b p.2 - energy a b p.1)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hg.sub hf
  simp_rw [range_inner]
  simpa only [Function.comp_def, abs_zero, neg_zero, zero_div, Real.exp_zero] using
    Real.continuous_exp.continuousAt.tendsto.comp (hd.abs.neg.div_const 8)

theorem gaussian_absolutelyContinuous_of_summable (a b : ℕ → ℝ)
    (hs : Summable (fun n => (a n - b n) ^ 2)) : gaussianProduct a ≪ gaussianProduct b := by
  apply MeasureEquivalenceProductAffinity.product_absolutelyContinuous_of_affinity_tendsto_one
    (fun n => blockRootLp (Finset.range n) a b)
    (fun n => blockRootLp_unit (Finset.range n) a b) (range_affinity_tendsto_one a b hs)
  intro I s hsm
  obtain ⟨k, hk⟩ := I.exists_nat_subset_range
  apply eventually_atTop.mpr
  refine ⟨k, fun n hn => ?_⟩
  have hi : (∫ x in cylinder I s, (blockRootLp (Finset.range n) a b x) ^ 2
      ∂gaussianProduct b) = ∫ x in cylinder I s, blockRoot (Finset.range n) a b x ^ 2
      ∂gaussianProduct b := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (blockRootLp_coe (Finset.range n) a b)] with x hx
    rw [hx]
  rw [hi]
  exact block_cylinder_density (hk.trans (Finset.range_mono hn)) a b hsm

theorem gaussian_mutualAC_of_summable (a b : ℕ → ℝ)
    (hs : Summable (fun n => (a n - b n) ^ 2)) :
    gaussianProduct a ≪ gaussianProduct b ∧ gaussianProduct b ≪ gaussianProduct a := by
  exact ⟨gaussian_absolutelyContinuous_of_summable a b hs,
    gaussian_absolutelyContinuous_of_summable b a (hs.congr (fun n => by ring))⟩

def blockTest (I : Finset ℕ) (a b : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {x | 1 ≤ blockRoot I a b x}

lemma measurableSet_blockTest (I : Finset ℕ) (a b : ℕ → ℝ) :
    MeasurableSet (blockTest I a b) :=
  measurableSet_le measurable_const (continuous_blockRoot I a b).measurable

lemma blockTest_error_Q (I : Finset ℕ) (a b : ℕ → ℝ) :
    gaussianProduct b (blockTest I a b) ≤
      ENNReal.ofReal (∫ x, blockRoot I a b x ∂gaussianProduct b) := by
  have hu := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (gaussian_product_block_memLp I a b)
  exact hu.measure_le_integral (ae_of_all _ (blockRoot_nonneg I a b)) (fun _ hx => hx)

lemma blockTest_error_P (I : Finset ℕ) (a b : ℕ → ℝ) :
    gaussianProduct a (blockTest I a b)ᶜ ≤
      ENNReal.ofReal (∫ x, blockRoot I a b x ∂gaussianProduct b) := by
  let s : Set (I → ℝ) := {y | 1 ≤ ∏ i : I, rootLikelihood (a i) (b i) (y i)}
  have hs : MeasurableSet s := by
    apply measurableSet_le measurable_const
    unfold rootLikelihood
    fun_prop
  have heq : gaussianProduct a (blockTest I a b)ᶜ =
      ENNReal.ofReal (∫ x in (blockTest I a b)ᶜ, blockRoot I a b x ^ 2
        ∂gaussianProduct b) :=
    (block_cylinder_density (I := I) (J := I) (by rfl) a b hs.compl).symm
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  have hu := MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (gaussian_product_block_memLp I a b)
  calc
    _ ≤ ∫ x in (blockTest I a b)ᶜ, blockRoot I a b x ∂gaussianProduct b := by
      apply setIntegral_mono_on (gaussian_product_block_memLp I a b).integrable_sq.restrict
        hu.restrict (measurableSet_blockTest I a b).compl
      intro x hx
      have hx' : blockRoot I a b x ≤ 1 := le_of_lt (lt_of_not_ge hx)
      simpa only [pow_two, mul_one] using
        mul_le_mul_of_nonneg_left hx' (blockRoot_nonneg I a b x)
    _ ≤ _ := integral_mono_measure Measure.restrict_le_self
      (ae_of_all _ (blockRoot_nonneg I a b)) hu

lemma gaussian_affinity_tendsto_zero_of_not_summable (a b : ℕ → ℝ)
    (hs : ¬Summable (fun n => (a n - b n) ^ 2)) :
    Tendsto (fun n => Real.exp (-energy a b n / 8)) atTop (𝓝 0) := by
  have hV : Tendsto (energy a b) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => sq_nonneg (a n - b n))).mp hs
  exact Real.tendsto_exp_atBot.comp
    (Filter.Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 8)
      (tendsto_neg_atTop_atBot.comp hV))

theorem gaussian_mutuallySingular_of_not_summable (a b : ℕ → ℝ)
    (hs : ¬Summable (fun n => (a n - b n) ^ 2)) :
    gaussianProduct a ⟂ₘ gaussianProduct b := by
  have ht := gaussian_affinity_tendsto_zero_of_not_summable a b hs
  have hex : ∀ k : ℕ, ∃ n : ℕ, Real.exp (-energy a b n / 8) ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    obtain ⟨n, hn⟩ := ((tendsto_order.mp ht).2 ((1 / 2 : ℝ) ^ k)
      (pow_pos (by norm_num) k)).exists
    exact ⟨n, hn.le⟩
  choose N hN using hex
  let A : ℕ → Set (ℕ → ℝ) := fun k => blockTest (Finset.range (N k)) a b
  have hA : ∀ k, MeasurableSet (A k) := fun k => measurableSet_blockTest _ a b
  have hint (k : ℕ) : ENNReal.ofReal
      (∫ x, blockRoot (Finset.range (N k)) a b x ∂gaussianProduct b) ≤
      (2⁻¹ : ℝ≥0∞) ^ k := by
    rw [gaussian_product_block_affinity,
      Finset.sum_coe_sort (Finset.range (N k)) (fun i : ℕ => (a i - b i) ^ 2)]
    calc
      _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := ENNReal.ofReal_le_ofReal (hN k)
      _ = _ := by simp [ENNReal.inv_pow]
  have hQ : (∑' k, gaussianProduct b (A k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.tsum_le_tsum
        (fun k => (blockTest_error_Q _ a b).trans (hint k))
      _ = 2 := ENNReal.tsum_geometric_two
  have hP : (∑' k, gaussianProduct a (A k)ᶜ) ≠ ∞ := by
    apply ne_top_of_le_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    calc
      _ ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ k := ENNReal.tsum_le_tsum
        (fun k => (blockTest_error_P _ a b).trans (hint k))
      _ = 2 := ENNReal.tsum_geometric_two
  exact (MeasureEquivalenceProductAffinity.mutuallySingular_of_summable_tests A hA hQ hP).symm

theorem gaussian_absolutelyContinuous_iff_summable (a b : ℕ → ℝ) :
    gaussianProduct a ≪ gaussianProduct b ↔ Summable (fun n => (a n - b n) ^ 2) := by
  refine ⟨fun hac => ?_, gaussian_absolutelyContinuous_of_summable a b⟩
  by_contra hs
  have hz := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hac
    (gaussian_mutuallySingular_of_not_summable a b hs)
  have hm := congrArg (fun μ : Measure (ℕ → ℝ) => μ Set.univ) hz
  simp at hm

theorem gaussian_mutualAC_iff_summable (a b : ℕ → ℝ) :
    (gaussianProduct a ≪ gaussianProduct b ∧ gaussianProduct b ≪ gaussianProduct a) ↔
      Summable (fun n => (a n - b n) ^ 2) :=
  ⟨fun h => (gaussian_absolutelyContinuous_iff_summable a b).mp h.1,
    gaussian_mutualAC_of_summable a b⟩

end MeasureEquivalenceGaussian
end MainProofScope4

/- Source module: GaussianContinuity -/
section MainProofScope5
/-! The actual Gaussian family is continuous for the product topology on real sequences
and the weak topology on probability measures. Together with GaussianCriterion this
is a continuous reduction of square-summable difference to mutual absolute continuity.
-/

open MeasureTheory ProbabilityTheory Filter Set BoundedContinuousFunction
open scoped ENNReal BigOperators Topology

namespace MeasureEquivalenceGaussian

noncomputable def gaussianProbability (a : ℕ → ℝ) : ProbabilityMeasure (ℕ → ℝ) :=
  ⟨gaussianProduct a, inferInstance⟩

lemma gaussianProduct_map_add (a b : ℕ → ℝ) :
    (gaussianProduct b).map (fun x => x + a) = gaussianProduct (b + a) := by
  unfold gaussianProduct
  convert Measure.infinitePi_map_pi (fun n => gaussianReal (b n) 1)
    (f := fun i x => x + a i) (fun i => measurable_id.add_const (a i)) using 1
  simp only [gaussianReal_map_add_const, Pi.add_apply]

lemma integral_gaussianProbability (a : ℕ → ℝ) (f : (ℕ → ℝ) →ᵇ ℝ) :
    (∫ x, f x ∂(gaussianProbability a)) =
      ∫ x, f (x + a) ∂(gaussianProduct 0) := by
  change (∫ x, f x ∂(gaussianProduct a)) = _
  have hm := gaussianProduct_map_add a 0
  simp only [zero_add] at hm
  rw [← hm]
  exact integral_map (continuous_id.add_const a).measurable.aemeasurable
    f.continuous.aestronglyMeasurable

theorem continuous_gaussianProbability : Continuous gaussianProbability := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro f
  simp_rw [integral_gaussianProbability]
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_integral_filter_of_norm_le_const
  · exact Eventually.of_forall (fun b =>
      (f.continuous.comp (continuous_id.add_const b)).aestronglyMeasurable)
  · exact ⟨‖f‖, Eventually.of_forall (fun b => ae_of_all _ (fun x => f.norm_coe_le_norm _))⟩
  · exact ae_of_all _ (fun x =>
      (f.continuous.comp (continuous_const.add continuous_id)).continuousAt)

theorem measurable_gaussianProbability :
    @Measurable (ℕ → ℝ) (ProbabilityMeasure (ℕ → ℝ)) _
      (borel (ProbabilityMeasure (ℕ → ℝ))) gaussianProbability :=
  continuous_gaussianProbability.borel_measurable.mono OpensMeasurableSpace.borel_le le_rfl

theorem gaussianProbability_mutualAC_iff (a b : ℕ → ℝ) :
    (((gaussianProbability a : Measure (ℕ → ℝ)) ≪ gaussianProbability b) ∧
      ((gaussianProbability b : Measure (ℕ → ℝ)) ≪ gaussianProbability a)) ↔
      Summable (fun n => (a n - b n) ^ 2) :=
  gaussian_mutualAC_iff_summable a b

theorem gaussian_continuous_reduction :
    Continuous gaussianProbability ∧ ∀ a b : ℕ → ℝ,
      Summable (fun n => (a n - b n) ^ 2) ↔
      (((gaussianProbability a : Measure (ℕ → ℝ)) ≪ gaussianProbability b) ∧
        ((gaussianProbability b : Measure (ℕ → ℝ)) ≪ gaussianProbability a)) :=
  ⟨continuous_gaussianProbability, fun a b => (gaussianProbability_mutualAC_iff a b).symm⟩


end MeasureEquivalenceGaussian
end MainProofScope5

/- Source module: GaussianCanonical -/
section MainProofScope6
/-! Measurability of the actual Gaussian family for the canonical evaluation
(Giry) measurable structure on measures and probability measures.
-/

open MeasureTheory

namespace MeasureEquivalenceGaussian

theorem measurable_gaussianProduct_canonical : Measurable gaussianProduct := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  have hm : Measurable (fun a : ℕ → ℝ =>
      gaussianProduct 0 ((fun x : ℕ → ℝ => x + a) ⁻¹' s)) := by
    have hset : MeasurableSet ((fun z : (ℕ → ℝ) × (ℕ → ℝ) => z.2 + z.1) ⁻¹' s) :=
      (measurable_snd.add measurable_fst) hs
    exact measurable_measure_prodMk_left hset
  have he : (fun a : ℕ → ℝ => gaussianProduct a s) =
      (fun a => gaussianProduct 0 ((fun x : ℕ → ℝ => x + a) ⁻¹' s)) := by
    funext a
    have hmap := gaussianProduct_map_add a 0
    simp only [zero_add] at hmap
    rw [← hmap]
    exact Measure.map_apply
      (show Measurable (fun x : ℕ → ℝ => x + a) from measurable_id.add_const a) hs
  rw [he]
  exact hm

theorem measurable_gaussianProbability_canonical : Measurable gaussianProbability :=
  measurable_gaussianProduct_canonical.subtype_mk


end MeasureEquivalenceGaussian
end MainProofScope6

/- Source module: HilbertCoordinates -/
section MainProofScope7
/-! Countable real coordinates for a separable real Hilbert space, preserving
the squared norm as an actual summable series. No infinite-dimensionality
assumption is used: unused natural-number coordinates are zero.
-/

open Set Filter TopologicalSpace
open scoped Topology InnerProductSpace ENNReal

namespace MeasureEquivalenceHilbertCoordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma orthonormal_index_countable [SeparableSpace H] {ι : Type*} {v : ι → H}
    (hv : Orthonormal ℝ v) : Countable ι := by
  have hd : Pairwise (fun i j => Disjoint (Metric.ball (v i) (1 / 3 : ℝ))
      (Metric.ball (v j) (1 / 3 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hn : ‖v i - v j‖ ^ 2 = 2 := by
      rw [norm_sub_sq_real, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

theorem exists_continuous_coordinates [CompleteSpace H] [SeparableSpace H] :
    ∃ F : H → (ℕ → ℝ), Continuous F ∧ ∀ x y : H,
      HasSum (fun n => (F x n - F y n) ^ 2) (‖x - y‖ ^ 2) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℝ H
  have : Countable w := orthonormal_index_countable b.orthonormal
  obtain ⟨e, he⟩ := exists_injective_nat w
  let F : H → (ℕ → ℝ) := fun x => Function.extend e (fun i => inner ℝ (b i) x) 0
  refine ⟨F, ?_, ?_⟩
  · apply continuous_pi
    intro n
    by_cases hn : n ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hn
      have hF : (fun x => F x (e i)) = (fun x => inner ℝ (b i) x) := by
        funext x
        exact he.extend_apply _ _ i
      rw [hF]
      fun_prop
    · have hF : (fun x => F x n) = (fun _ : H => (0 : ℝ)) := by
        funext x
        exact Function.extend_apply' _ _ _ hn
      rw [hF]
      exact continuous_const
  · intro x y
    have hb : HasSum (fun i => (inner ℝ (b i) x - inner ℝ (b i) y) ^ 2)
        (‖x - y‖ ^ 2) := by
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
        b.repr_apply_apply, inner_sub_right, b.repr.norm_map] using
        lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr (x - y))
    have hF : (fun n => (F x n - F y n) ^ 2) =
        Function.extend e (fun i => (inner ℝ (b i) x - inner ℝ (b i) y) ^ 2) 0 := by
      funext n
      by_cases hn : n ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hn
        simp only [F, he.extend_apply]
      · simp only [F, Function.extend_apply' _ _ _ hn, Pi.zero_apply, sub_self]
        norm_num
    rw [hF]
    exact (hasSum_extend_zero he).2 hb


end MeasureEquivalenceHilbertCoordinates
end MainProofScope7

/- Source module: SnowflakeIntegral -/
section MainProofScope8
/-! Concrete weighted-exponential Hilbert snowflake on the positive half-line.
This file is developed separately from the frozen Gaussian proof sources.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureEquivalenceSnowflake

noncomputable def oscillation (t s : ℝ) : ℂ :=
  Complex.exp (Complex.I * (s * t : ℝ)) - 1

noncomputable def raw (p t s : ℝ) : ℂ :=
  (s ^ (-(1 + p) / 2) : ℝ) • oscillation t s

noncomputable def halfLine : Measure ℝ := volume.restrict (Ioi 0)

lemma measurable_oscillation (t : ℝ) : Measurable (oscillation t) := by
  unfold oscillation
  fun_prop

lemma measurable_raw (p t : ℝ) : Measurable (raw p t) := by
  unfold raw
  exact (measurable_id.pow_const _).smul (measurable_oscillation t)

lemma oscillation_norm_le_linear (t s : ℝ) : ‖oscillation t s‖ ≤ ‖s * t‖ :=
  Real.norm_exp_I_mul_ofReal_sub_one_le

lemma oscillation_norm_le_two (t s : ℝ) : ‖oscillation t s‖ ≤ 2 := by
  calc
    _ ≤ ‖Complex.exp (Complex.I * (s * t : ℝ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal]; norm_num

lemma raw_norm_sq (p t s : ℝ) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 = ‖oscillation t s‖ ^ 2 * s ^ (-1 - p) := by
  have hw : (s ^ (-(1 + p) / 2) : ℝ) ^ 2 = s ^ (-1 - p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    congr 1
    norm_num
    ring
  rw [raw, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hs.le _), mul_pow, hw]
  ring

lemma raw_norm_sq_le_local (p t s : ℝ) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 ≤ t ^ 2 * s ^ (1 - p) := by
  have hn := oscillation_norm_le_linear t s
  have hsq : ‖oscillation t s‖ ^ 2 ≤ (s * t) ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hp : s ^ 2 * s ^ (-1 - p) = s ^ (1 - p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    congr 1
    norm_num
    ring
  rw [raw_norm_sq p t s hs]
  calc
    _ ≤ (s * t) ^ 2 * s ^ (-1 - p) :=
      mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hs.le _)
    _ = t ^ 2 * (s ^ 2 * s ^ (-1 - p)) := by ring
    _ = t ^ 2 * s ^ (1 - p) := by rw [hp]

lemma raw_norm_sq_le_tail (p t s : ℝ) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 ≤ 4 * s ^ (-1 - p) := by
  rw [raw_norm_sq p t s hs]
  exact mul_le_mul_of_nonneg_right
    (by convert pow_le_pow_left₀ (norm_nonneg _) (oscillation_norm_le_two t s) 2 using 1; norm_num)
    (Real.rpow_nonneg hs.le _)

lemma integrable_raw_norm_sq (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    Integrable (fun s => ‖raw p t s‖ ^ 2) halfLine := by
  have hm := (measurable_raw p t).norm.pow_const 2
  have hlocal : IntegrableOn (fun s => ‖raw p t s‖ ^ 2) (Ioo 0 1) := by
    have hb : IntegrableOn (fun s : ℝ => t ^ 2 * s ^ (1 - p)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)).const_mul _
    refine hb.mono' hm.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact raw_norm_sq_le_local p t s hs.1)
  have htail : IntegrableOn (fun s => ‖raw p t s‖ ^ 2) (Ioi 1) := by
    have hb : IntegrableOn (fun s : ℝ => 4 * s ^ (-1 - p)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hb.mono' hm.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact raw_norm_sq_le_tail p t s (lt_trans zero_lt_one hs))
  change IntegrableOn (fun s => ‖raw p t s‖ ^ 2) (Ioi (0 : ℝ)) volume
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  exact ((integrableOn_Ioc_iff_integrableOn_Ioo).2 hlocal).union htail

lemma memLp_raw (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    MemLp (raw p t) 2 halfLine :=
  (memLp_two_iff_integrable_sq_norm (measurable_raw p t).aestronglyMeasurable).2
    (integrable_raw_norm_sq p hp0 hp2 t)

noncomputable def embedding (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    Lp ℂ 2 halfLine := (memLp_raw p hp0 hp2 t).toLp (raw p t)

lemma oscillation_norm_neg (t s : ℝ) : ‖oscillation (-t) s‖ = ‖oscillation t s‖ := by
  simp only [oscillation, Complex.norm_exp_I_mul_ofReal_sub_one, mul_neg,
    neg_div, Real.sin_neg, mul_neg, norm_neg]

lemma raw_norm_neg (p t s : ℝ) : ‖raw p (-t) s‖ = ‖raw p t s‖ := by
  simp only [raw, norm_smul, oscillation_norm_neg]

lemma oscillation_sub_factor (t u s : ℝ) :
    oscillation t s - oscillation u s =
      Complex.exp (Complex.I * (s * u : ℝ)) * oscillation (t - u) s := by
  unfold oscillation
  rw [mul_sub, ← Complex.exp_add]
  have he : Complex.I * (s * u : ℝ) + Complex.I * (s * (t - u) : ℝ) =
      Complex.I * (s * t : ℝ) := by push_cast; ring
  rw [he]
  ring

lemma raw_sub_norm (p t u s : ℝ) : ‖raw p t s - raw p u s‖ = ‖raw p (t - u) s‖ := by
  simp only [raw, ← smul_sub, norm_smul]
  rw [oscillation_sub_factor, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

noncomputable def energy (p t : ℝ) : ℝ := ∫ s, ‖raw p t s‖ ^ 2 ∂halfLine

lemma energy_neg (p t : ℝ) : energy p (-t) = energy p t := by
  simp only [energy, raw_norm_neg]

lemma raw_norm_sq_dilation (p t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    ‖raw p t s‖ ^ 2 = t ^ (1 + p) * ‖raw p 1 (t * s)‖ ^ 2 := by
  rw [raw_norm_sq p t s hs, raw_norm_sq p 1 (t * s) (mul_pos ht hs),
    Real.mul_rpow ht.le hs.le]
  have ho : oscillation 1 (t * s) = oscillation t s := by simp [oscillation, mul_comm]
  have ht' : t ^ (1 + p) * t ^ (-1 - p) = (1 : ℝ) := by
    rw [← Real.rpow_add ht]
    have he : (1 + p) + (-1 - p) = 0 := by ring
    rw [he, Real.rpow_zero]
  rw [ho]
  symm
  calc
    _ = (t ^ (1 + p) * t ^ (-1 - p)) * (‖oscillation t s‖ ^ 2 * s ^ (-1 - p)) := by ring
    _ = _ := by rw [ht', one_mul]

lemma energy_pos_dilation (p t : ℝ) (ht : 0 < t) :
    energy p t = t ^ p * energy p 1 := by
  have hraw : (fun s => ‖raw p t s‖ ^ 2) =ᵐ[halfLine]
      (fun s => t ^ (1 + p) * ‖raw p 1 (t * s)‖ ^ 2) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun s hs => raw_norm_sq_dilation p t s ht hs)
  unfold energy
  rw [integral_congr_ae hraw, integral_const_mul]
  change t ^ (1 + p) * (∫ s in Ioi (0 : ℝ), ‖raw p 1 (t * s)‖ ^ 2) = _
  rw [integral_comp_mul_left_Ioi (fun s => ‖raw p 1 s‖ ^ 2) 0 ht]
  simp only [mul_zero, smul_eq_mul]
  have ht' : t ^ (1 + p) * t⁻¹ = t ^ p := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    congr 1
    ring
  rw [← mul_assoc, ht']
  rfl

lemma energy_abs (p : ℝ) (hp0 : 0 < p) (t : ℝ) :
    energy p t = |t| ^ p * energy p 1 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [abs_of_neg ht, ← energy_neg p t]
    exact energy_pos_dilation p (-t) (neg_pos.mpr ht)
  · simp [energy, raw, oscillation, Real.zero_rpow hp0.ne']
  · rw [abs_of_pos ht]
    exact energy_pos_dilation p t ht

lemma energy_one_pos (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) : 0 < energy p 1 := by
  apply (integral_pos_iff_support_of_nonneg (fun s => sq_nonneg _)
    (integrable_raw_norm_sq p hp0 hp2 1)).2
  have hsub : Ioo 0 Real.pi ⊆ Function.support (fun s => ‖raw p 1 s‖ ^ 2) := by
    intro s hs
    change ‖raw p 1 s‖ ^ 2 ≠ 0
    have hsin : 0 < Real.sin (s / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.1]) (by linarith [hs.2, Real.pi_pos])
    have ho : 0 < ‖oscillation 1 s‖ := by
      rw [oscillation, Complex.norm_exp_I_mul_ofReal_sub_one, mul_one, Real.norm_eq_abs]
      exact abs_pos.mpr (mul_ne_zero two_ne_zero hsin.ne')
    rw [raw_norm_sq p 1 s hs.1]
    exact (mul_pos (pow_pos ho _) (Real.rpow_pos_of_pos hs.1 _)).ne'
  have hm : 0 < halfLine (Ioo 0 Real.pi) := by
    rw [halfLine, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr Ioo_subset_Ioi_self, Real.volume_Ioo, sub_zero]
    exact ENNReal.ofReal_pos.mpr Real.pi_pos
  exact hm.trans_le (measure_mono hsub)

lemma embedding_coe (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t : ℝ) :
    embedding p hp0 hp2 t =ᵐ[halfLine] raw p t :=
  (memLp_raw p hp0 hp2 t).coeFn_toLp

lemma lp_norm_sq (f : Lp ℂ 2 halfLine) : ‖f‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂halfLine := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem embedding_norm_sub_sq (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t u : ℝ) :
    ‖embedding p hp0 hp2 t - embedding p hp0 hp2 u‖ ^ 2 =
      energy p 1 * |t - u| ^ p := by
  rw [lp_norm_sq]
  have hnorm : (fun s => ‖(embedding p hp0 hp2 t - embedding p hp0 hp2 u) s‖ ^ 2)
      =ᵐ[halfLine] (fun s => ‖raw p (t - u) s‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub (embedding p hp0 hp2 t) (embedding p hp0 hp2 u),
      embedding_coe p hp0 hp2 t, embedding_coe p hp0 hp2 u] with s hs ht hu
    simp only [hs, Pi.sub_apply, ht, hu, raw_sub_norm]
  rw [integral_congr_ae hnorm]
  exact (energy_abs p hp0 (t - u)).trans (mul_comm _ _)

theorem embedding_dist (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) (t u : ℝ) :
    dist (embedding p hp0 hp2 t) (embedding p hp0 hp2 u) =
      Real.sqrt (energy p 1 * |t - u| ^ p) := by
  rw [← embedding_norm_sub_sq p hp0 hp2 t u, Real.sqrt_sq (norm_nonneg _), dist_eq_norm]

theorem continuous_embedding (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) :
    Continuous (embedding p hp0 hp2) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp_rw [embedding_dist]
  have hc : Continuous (fun u : ℝ => Real.sqrt (energy p 1 * |u - t| ^ p)) :=
    Real.continuous_sqrt.comp (continuous_const.mul
      ((continuous_id.sub continuous_const).abs.rpow_const (fun _ => Or.inr hp0.le)))
  simpa only [sub_self, abs_zero, Real.zero_rpow hp0.ne', mul_zero, Real.sqrt_zero]
    using hc.tendsto t


end MeasureEquivalenceSnowflake
end MainProofScope8

/- Source module: SnowflakeReduction -/
section MainProofScope9
/-! Actual continuous reductions of p-summable difference to square-summable
difference on the ambient product space of all real sequences.
-/

open MeasureTheory Filter Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureEquivalenceSnowflake

instance halfLine_sigmaFinite : SigmaFinite halfLine := by
  unfold halfLine
  infer_instance

theorem exists_continuous_sequence_snowflake (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) :
    ∃ J : ℝ → (ℕ → ℝ), Continuous J ∧ ∀ t u : ℝ,
      HasSum (fun k => (J t k - J u k) ^ 2) (energy p 1 * |t - u| ^ p) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨F, hF, hnorm⟩ :=
    MeasureEquivalenceHilbertCoordinates.exists_continuous_coordinates
      (H := Lp ℂ 2 halfLine)
  refine ⟨fun t => F (embedding p hp0 hp2 t), hF.comp (continuous_embedding p hp0 hp2), ?_⟩
  intro t u
  simpa only [embedding_norm_sub_sq] using
    hnorm (embedding p hp0 hp2 t) (embedding p hp0 hp2 u)

theorem exists_continuous_reduction_to_square (p : ℝ) (hp0 : 0 < p) (hp2 : p < 2) :
    ∃ R : (ℕ → ℝ) → (ℕ → ℝ), Continuous R ∧ ∀ x y : ℕ → ℝ,
      Summable (fun n => |x n - y n| ^ p) ↔
        Summable (fun m => (R x m - R y m) ^ 2) := by
  obtain ⟨J, hJ, hrow⟩ := exists_continuous_sequence_snowflake p hp0 hp2
  let R : (ℕ → ℝ) → (ℕ → ℝ) := fun x m => J (x (Nat.unpair m).1) (Nat.unpair m).2
  refine ⟨R, ?_, ?_⟩
  · apply continuous_pi
    intro m
    exact (continuous_apply (Nat.unpair m).2).comp (hJ.comp (continuous_apply (Nat.unpair m).1))
  · intro x y
    have hflat : Summable (fun m => (R x m - R y m) ^ 2) ↔
        Summable (fun q : ℕ × ℕ => (J (x q.1) q.2 - J (y q.1) q.2) ^ 2) := by
      change Summable ((fun q : ℕ × ℕ => (J (x q.1) q.2 - J (y q.1) q.2) ^ 2) ∘
        Nat.pairEquiv.symm) ↔ _
      exact Nat.pairEquiv.symm.summable_iff
    have hprod := summable_prod_of_nonneg
      (f := fun q : ℕ × ℕ => (J (x q.1) q.2 - J (y q.1) q.2) ^ 2)
      (fun q => sq_nonneg _)
    have hsum : (fun n => ∑' k, (J (x n) k - J (y n) k) ^ 2) =
        (fun n => energy p 1 * |x n - y n| ^ p) :=
      funext (fun n => (hrow (x n) (y n)).tsum_eq)
    rw [hflat, hprod, hsum]
    constructor
    · intro h
      exact ⟨fun n => (hrow (x n) (y n)).summable, h.mul_left _⟩
    · intro h
      exact (summable_mul_left_iff (energy_one_pos p hp0 hp2).ne').1 h.2


end MeasureEquivalenceSnowflake
end MainProofScope9

/- Source module: GaussianPositive -/
section MainProofScope10
/-! Positive continuous reductions for p-summable difference, 0<p<=2,
to actual mutual absolute continuity on ProbabilityMeasure (Nat -> Real).
The sample-space transfer to Cantor space is a separate statement.
-/

open MeasureTheory
open scoped Topology

namespace MeasureEquivalenceGaussian

theorem exists_continuous_gaussian_reduction_of_pos_le_two (p : ℝ)
    (hp0 : 0 < p) (hp2 : p ≤ 2) :
    ∃ G : (ℕ → ℝ) → ProbabilityMeasure (ℕ → ℝ), Continuous G ∧ Measurable G ∧ ∀ x y : ℕ → ℝ,
      Summable (fun n => |x n - y n| ^ p) ↔
        (((G x : Measure (ℕ → ℝ)) ≪ G y) ∧ ((G y : Measure (ℕ → ℝ)) ≪ G x)) := by
  by_cases hp : p = 2
  · subst p
    refine ⟨gaussianProbability, continuous_gaussianProbability,
      measurable_gaussianProbability_canonical, ?_⟩
    intro x y
    simpa only [Real.rpow_two, sq_abs] using (gaussianProbability_mutualAC_iff x y).symm
  · obtain ⟨R, hR, hiff⟩ := MeasureEquivalenceSnowflake.exists_continuous_reduction_to_square
      p hp0 (lt_of_le_of_ne hp2 hp)
    refine ⟨fun x => gaussianProbability (R x), continuous_gaussianProbability.comp hR,
      measurable_gaussianProbability_canonical.comp hR.measurable, ?_⟩
    intro x y
    exact (hiff x y).trans (gaussianProbability_mutualAC_iff (R x) (R y)).symm

theorem exists_continuous_gaussian_reduction_one_le (p : ℝ)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2) :
    ∃ G : (ℕ → ℝ) → ProbabilityMeasure (ℕ → ℝ), Continuous G ∧ Measurable G ∧ ∀ x y : ℕ → ℝ,
      Summable (fun n => |x n - y n| ^ p) ↔
        (((G x : Measure (ℕ → ℝ)) ≪ G y) ∧ ((G y : Measure (ℕ → ℝ)) ≪ G x)) :=
  exists_continuous_gaussian_reduction_of_pos_le_two p (lt_of_lt_of_le zero_lt_one hp1) hp2


end MeasureEquivalenceGaussian
end MainProofScope10

/- Source module: SampleSpaceTransport -/
section MainProofScope11
open MeasureTheory

noncomputable section

namespace MeasureEquivalenceSampleSpace

variable {X Y A : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace A]

/-- Push a probability forward along an actual measurable equivalence. -/
def pushProbability (e : X ≃ᵐ Y) (μ : ProbabilityMeasure X) : ProbabilityMeasure Y :=
  ⟨(μ : Measure X).map e, (μ : Measure X).isProbabilityMeasure_map e.measurable.aemeasurable⟩

theorem measurable_pushProbability (e : X ≃ᵐ Y) : Measurable (pushProbability e) :=
  ((Measure.measurable_map e e.measurable).comp measurable_subtype_coe).subtype_mk

@[simp] theorem pushProbability_symm (e : X ≃ᵐ Y) (μ : ProbabilityMeasure X) :
    pushProbability e.symm (pushProbability e μ) = μ := by
  apply Subtype.ext
  exact MeasurableEquiv.map_symm_map e

/-- The canonical evaluation/Giry spaces of probabilities are measurably equivalent. -/
def probabilityEquiv (e : X ≃ᵐ Y) : ProbabilityMeasure X ≃ᵐ ProbabilityMeasure Y where
  toEquiv :=
    { toFun := pushProbability e
      invFun := pushProbability e.symm
      left_inv := pushProbability_symm e
      right_inv := pushProbability_symm e.symm }
  measurable_toFun := measurable_pushProbability e
  measurable_invFun := measurable_pushProbability e.symm

theorem pushProbability_ac_iff (e : X ≃ᵐ Y) (μ ν : ProbabilityMeasure X) :
    (pushProbability e μ : Measure Y) ≪ pushProbability e ν ↔ (μ : Measure X) ≪ ν := by
  constructor
  · intro h
    have h' := e.symm.measurableEmbedding.absolutelyContinuous_map h
    change ((μ : Measure X).map e).map e.symm ≪ ((ν : Measure X).map e).map e.symm at h'
    simpa only [MeasurableEquiv.map_symm_map] using h'
  · exact e.measurableEmbedding.absolutelyContinuous_map

theorem pushProbability_mutual_ac_iff (e : X ≃ᵐ Y) (μ ν : ProbabilityMeasure X) :
    ((pushProbability e μ : Measure Y) ≪ pushProbability e ν ∧
      (pushProbability e ν : Measure Y) ≪ pushProbability e μ) ↔
    ((μ : Measure X) ≪ ν ∧ (ν : Measure X) ≪ μ) := by
  rw [pushProbability_ac_iff, pushProbability_ac_iff]

theorem transfer_reduction (e : X ≃ᵐ Y) (R : A → A → Prop)
    (f : A → ProbabilityMeasure X) (hf : Measurable f)
    (hred : ∀ x y, R x y ↔ ((f x : Measure X) ≪ f y ∧ (f y : Measure X) ≪ f x)) :
    ∃ g : A → ProbabilityMeasure Y, Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure Y) ≪ g y ∧ (g y : Measure Y) ≪ g x) := by
  refine ⟨pushProbability e ∘ f, (measurable_pushProbability e).comp hf, ?_⟩
  intro x y
  exact (hred x y).trans (pushProbability_mutual_ac_iff e (f x) (f y)).symm

theorem exists_reduction_iff (e : X ≃ᵐ Y) (R : A → A → Prop) :
    (∃ f : A → ProbabilityMeasure X, Measurable f ∧
      ∀ x y, R x y ↔ ((f x : Measure X) ≪ f y ∧ (f y : Measure X) ≪ f x)) ↔
    (∃ g : A → ProbabilityMeasure Y, Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure Y) ≪ g y ∧ (g y : Measure Y) ≪ g x)) := by
  constructor
  · rintro ⟨f, hf, hred⟩
    exact transfer_reduction e R f hf hred
  · rintro ⟨f, hf, hred⟩
    exact transfer_reduction e.symm R f hf hred

theorem realSequence_not_countable : ¬ Countable (ℕ → ℝ) := by
  intro h
  let := h
  have hreal : Countable ℝ := Function.Injective.countable
    (f := fun r : ℝ => fun _ : ℕ => r) (by
      intro r s hrs
      exact congrFun hrs 0)
  exact not_countable (α := ℝ) hreal

def realSequenceEquivCantor : (ℕ → ℝ) ≃ᵐ (ℕ → Bool) :=
  PolishSpace.measurableEquivNatBoolOfNotCountable realSequence_not_countable

def realSequenceEquiv (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y]
    (hY : ¬ Countable Y) : (ℕ → ℝ) ≃ᵐ Y :=
  PolishSpace.measurableEquivOfNotCountable realSequence_not_countable hY

theorem transfer_real_sequence_reduction_to_cantor (R : A → A → Prop)
    (f : A → ProbabilityMeasure (ℕ → ℝ)) (hf : Measurable f)
    (hred : ∀ x y, R x y ↔ ((f x : Measure (ℕ → ℝ)) ≪ f y ∧
      (f y : Measure (ℕ → ℝ)) ≪ f x)) :
    ∃ g : A → ProbabilityMeasure (ℕ → Bool), Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure (ℕ → Bool)) ≪ g y ∧
        (g y : Measure (ℕ → Bool)) ≪ g x) :=
  transfer_reduction realSequenceEquivCantor R f hf hred

theorem transfer_real_sequence_reduction [StandardBorelSpace Y] (hY : ¬ Countable Y)
    (R : A → A → Prop) (f : A → ProbabilityMeasure (ℕ → ℝ)) (hf : Measurable f)
    (hred : ∀ x y, R x y ↔ ((f x : Measure (ℕ → ℝ)) ≪ f y ∧
      (f y : Measure (ℕ → ℝ)) ≪ f x)) :
    ∃ g : A → ProbabilityMeasure Y, Measurable g ∧
      ∀ x y, R x y ↔ ((g x : Measure Y) ≪ g y ∧ (g y : Measure Y) ≪ g x) :=
  transfer_reduction (realSequenceEquiv Y hY) R f hf hred

end MeasureEquivalenceSampleSpace
end
end MainProofScope11

/- Source module: KernelEquivalence -/
section MainProofScope12
/-!
Formal check of the conditional-measure step used in compact averaging.
This file does not claim to formalize the complete nonreducibility proof.
The equivalence relation here is literally mutual absolute continuity.
-/

open MeasureTheory ProbabilityTheory Filter

namespace MeasureEquivalenceResearch

def EquivalentMeasures {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) : Prop := mu ≪ nu ∧ nu ≪ mu

theorem map_base_compProd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) [IsFiniteMeasure mu]
    (kappa : Kernel X Y) [IsFiniteKernel kappa]
    (e : X ≃ᵐ X) (he : MeasurePreserving e mu mu) :
    (mu ⊗ₘ kappa).map (Prod.map e id) =
      mu ⊗ₘ kappa.comap e.symm e.symm.measurable := by
  apply Measure.ext_prod
  intro s t hs ht
  rw [Measure.map_apply (e.measurable.prodMap measurable_id) (hs.prod ht)]
  have hpre : (Prod.map e id) ⁻¹' (s ×ˢ t) = (e ⁻¹' s) ×ˢ t := by
    ext p
    rfl
  rw [hpre, Measure.compProd_apply_prod (e.measurable hs) ht,
    Measure.compProd_apply_prod hs ht]
  simpa only [Kernel.comap_apply, Function.comp_apply, e.symm_apply_apply] using
    he.setLIntegral_comp_preimage hs
      ((kappa.measurable_coe ht).comp e.symm.measurable)

theorem equivalent_compProd_iff
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (mu : Measure X) [SFinite mu] (kappa eta : Kernel X Y)
    [IsFiniteKernel kappa] [IsFiniteKernel eta] :
    EquivalentMeasures (mu ⊗ₘ kappa) (mu ⊗ₘ eta) ↔
      ∀ᵐ x ∂mu, EquivalentMeasures (kappa x) (eta x) := by
  unfold EquivalentMeasures
  rw [Measure.absolutelyContinuous_compProd_right_iff,
    Measure.absolutelyContinuous_compProd_right_iff]
  exact eventually_and.symm

theorem exact_kernel_cosets
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (mu : Measure G) [IsProbabilityMeasure mu]
    (H : AddSubgroup G) (kappa eta : Kernel G Y)
    [IsFiniteKernel kappa] [IsFiniteKernel eta]
    (g : G)
    (htranslate : ∀ x, eta x = kappa (x - g))
    (hreduction : ∀ x y, EquivalentMeasures (kappa x) (kappa y) ↔ x - y ∈ H) :
    EquivalentMeasures (mu ⊗ₘ eta) (mu ⊗ₘ kappa) ↔ g ∈ H := by
  rw [equivalent_compProd_iff]
  have hpoint : ∀ x, EquivalentMeasures (eta x) (kappa x) ↔ g ∈ H := by
    intro x
    rw [htranslate, hreduction]
    have hx : x - g - x = -g := by abel
    rw [hx, H.neg_mem_iff]
  simp_rw [hpoint]
  simp

theorem exact_quasi_invariance_of_kernel_reduction
    {G Y : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableSpace Y]
    [MeasurableAdd G]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (mu : Measure G) [IsProbabilityMeasure mu] [Measure.IsAddLeftInvariant mu]
    (H : AddSubgroup G) (kappa : Kernel G Y) [IsFiniteKernel kappa]
    (hreduction : ∀ x y, EquivalentMeasures (kappa x) (kappa y) ↔ x - y ∈ H)
    (g : G) :
    EquivalentMeasures ((mu ⊗ₘ kappa).map (fun p => (g + p.1, p.2)))
      (mu ⊗ₘ kappa) ↔ g ∈ H := by
  change EquivalentMeasures
    ((mu ⊗ₘ kappa).map (Prod.map (MeasurableEquiv.addLeft g) id))
    (mu ⊗ₘ kappa) ↔ g ∈ H
  rw [map_base_compProd mu kappa (MeasurableEquiv.addLeft g)
    (measurePreserving_add_left mu g)]
  apply exact_kernel_cosets mu H kappa _ g _ hreduction
  intro x
  simp [Kernel.comap_apply, sub_eq_add_neg, add_comm]


end MeasureEquivalenceResearch
end MainProofScope12

/- Source module: CompactAveraging -/
section MainProofScope13
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceCompactAveraging

/-!
`ProbabilityMeasure Y` carries mathlib's canonical evaluation/Giry measurable
structure. A measurable probability-valued map therefore supplies an actual
Markov kernel without any extra kernel hypothesis. The Haar normalization,
joint probability, and exact translation quasi-invariance are constructed
below, including the concrete compact torus and a continuous action adapter.
-/

open MeasureEquivalenceResearch

section Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def probabilityKernel (f : X → ProbabilityMeasure Y) (hf : Measurable f) : Kernel X Y where
  toFun x := (f x : Measure Y)
  measurable' := measurable_subtype_coe.comp hf

@[simp] lemma probabilityKernel_apply (f : X → ProbabilityMeasure Y) (hf : Measurable f)
    (x : X) : probabilityKernel f hf x = (f x : Measure Y) := rfl

instance probabilityKernel_markov (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    IsMarkovKernel (probabilityKernel f hf) where
  isProbabilityMeasure x := (f x).property

def averagedMeasure (μ : Measure X) (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    Measure (X × Y) := μ ⊗ₘ probabilityKernel f hf

instance averagedMeasure_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    IsProbabilityMeasure (averagedMeasure μ f hf) := by
  unfold averagedMeasure
  infer_instance

lemma averagedMeasure_apply_prod (μ : Measure X) [SFinite μ]
    (f : X → ProbabilityMeasure Y) (hf : Measurable f)
    {s : Set X} {t : Set Y} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    averagedMeasure μ f hf (s ×ˢ t) = ∫⁻ x in s, (f x : Measure Y) t ∂μ := by
  exact Measure.compProd_apply_prod hs ht

end Kernel

section CompactGroup

variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the actual compact whole group. -/
def compactHaar : Measure G := Measure.addHaarMeasure (⊤ : PositiveCompacts G)

instance compactHaar_probability : IsProbabilityMeasure (compactHaar G) := by
  constructor
  simpa [compactHaar] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))

instance compactHaar_invariant : Measure.IsAddLeftInvariant (compactHaar G) := by
  unfold compactHaar
  infer_instance

variable {G} {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]

theorem exact_quasi_invariance_of_probability_reduction
    (H : AddSubgroup G) (f : G → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H)
    (g : G) :
    EquivalentMeasures
      ((averagedMeasure (compactHaar G) f hf).map (fun z => (g + z.1, z.2)))
      (averagedMeasure (compactHaar G) f hf) ↔ g ∈ H := by
  exact exact_quasi_invariance_of_kernel_reduction (compactHaar G) H
    (probabilityKernel f hf) hred g

end CompactGroup

section Action

/-- The multiplicative-tag action used to feed the additive averaging measure to RNGraph. -/
abbrev baseTranslationAction (G Y : Type*) [AddMonoid G] :
    MulAction (Multiplicative G) (G × Y) where
  smul g z := (g.toAdd + z.1, z.2)
  one_smul z := by
    change (0 + z.1, z.2) = z
    simp
  mul_smul g h z := by
    change (g.toAdd + h.toAdd + z.1, z.2) = (g.toAdd + (h.toAdd + z.1), z.2)
    rw [add_assoc]

theorem continuous_baseTranslationAction (G Y : Type*)
    [AddMonoid G] [TopologicalSpace G] [ContinuousAdd G] [TopologicalSpace Y] :
    letI := baseTranslationAction G Y
    ContinuousSMul (Multiplicative G) (G × Y) := by
  let _ := baseTranslationAction G Y
  constructor
  change Continuous (fun z : Multiplicative G × (G × Y) =>
    (z.1.toAdd + z.2.1, z.2.2))
  exact ((continuous_toAdd.comp continuous_fst).add
    (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)

theorem exact_quasi_invariance_action
    {G Y : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]
    (H : AddSubgroup G) (f : G → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    letI := baseTranslationAction G Y
    ∀ g : Multiplicative G,
      EquivalentMeasures ((averagedMeasure (compactHaar G) f hf).map (fun z => g • z))
        (averagedMeasure (compactHaar G) f hf) ↔ g.toAdd ∈ H := by
  intro g
  exact exact_quasi_invariance_of_probability_reduction H f hf hred g.toAdd

end Action

abbrev Torus := ℕ → UnitAddCircle

example : CompactSpace Torus := inferInstance
example : MeasurableSpace Torus := inferInstance
example : BorelSpace Torus := inferInstance
example : PolishSpace Torus := inferInstance

theorem torus_averaging
    {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
    (H : AddSubgroup Torus) (f : Torus → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    ∃ M : Measure (Torus × Y), IsProbabilityMeasure M ∧
      ∀ g : Torus, EquivalentMeasures (M.map (fun z => (g + z.1, z.2))) M ↔ g ∈ H := by
  exact ⟨averagedMeasure (compactHaar Torus) f hf, inferInstance,
    exact_quasi_invariance_of_probability_reduction H f hf hred⟩

/-- Actual Polish sample-space version with the RNGraph-compatible action. -/
theorem torus_polish_action_averaging
    {Y : Type*} [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (H : AddSubgroup Torus) (f : Torus → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, EquivalentMeasures (f x : Measure Y) (f y : Measure Y) ↔ x - y ∈ H) :
    letI := baseTranslationAction Torus Y
    ∃ M : Measure (Torus × Y), IsProbabilityMeasure M ∧
      ∀ g : Multiplicative Torus,
        (M.map (fun z => g • z) ≪ M ∧ M ≪ M.map (fun z => g • z)) ↔ g.toAdd ∈ H := by
  exact ⟨averagedMeasure (compactHaar Torus) f hf, inferInstance,
    exact_quasi_invariance_action H f hf hred⟩


end MeasureEquivalenceCompactAveraging
end
end MainProofScope13

/- Source module: DensityMeasure -/
section MainProofScope14
/-! Concrete finite measures with an L2 square density. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureEquivalenceDensity

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

lemma integrable_square (f : Lp ℝ 2 μ) : Integrable (fun x => f x ^ 2) μ :=
  (L1.integrable_coeFn (square μ f)).congr (square_coe μ f)

noncomputable def squareMeasure (f : Lp ℝ 2 μ) : FiniteMeasure α :=
  ⟨μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)),
    isFiniteMeasure_withDensity_ofReal (integrable_square μ f).hasFiniteIntegral⟩

theorem squareMeasure_ac (f : Lp ℝ 2 μ) :
    (squareMeasure μ f : Measure α) ≪ μ :=
  withDensity_absolutelyContinuous _ _

theorem squareMeasure_injective_nonnegative [SigmaFinite μ] :
    Set.InjOn (squareMeasure μ) (Set.Ici (0 : Lp ℝ 2 μ)) := by
  intro f hf g hg hfg
  have heq : μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2)) =
      μ.withDensity (fun x => ENNReal.ofReal (g x ^ 2)) :=
    congrArg (fun ν : FiniteMeasure α => (ν : Measure α)) hfg
  have hae := (withDensity_eq_iff_of_sigmaFinite
    ((Lp.aestronglyMeasurable f).aemeasurable.pow_const 2).ennreal_ofReal
    ((Lp.aestronglyMeasurable g).aemeasurable.pow_const 2).ennreal_ofReal).mp heq
  apply Lp.ext
  filter_upwards [hae, (Lp.coeFn_nonneg f).mpr hf,
    (Lp.coeFn_nonneg g).mpr hg] with x h1 h2 h3
  change 0 ≤ f x at h2
  change 0 ≤ g x at h3
  have hs := congrArg ENNReal.toReal h1
  simp only [ENNReal.toReal_ofReal (sq_nonneg (f x)),
    ENNReal.toReal_ofReal (sq_nonneg (g x))] at hs
  nlinarith

theorem squareMeasure_integral (f : Lp ℝ 2 μ) (g : α → ℝ) :
    ∫ x, g x ∂(squareMeasure μ f : Measure α) = ∫ x, f x ^ 2 * g x ∂μ := by
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x ^ 2))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((Lp.aestronglyMeasurable f).aemeasurable.pow_const 2).ennreal_ofReal
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  simp [ENNReal.toReal_ofReal, sq_nonneg, smul_eq_mul]

theorem squareMeasure_continuous [TopologicalSpace α] [BorelSpace α] :
    Continuous (squareMeasure μ) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro g
  let gLp : Lp ℝ ∞ μ := (g.memLp_top (μ := μ)).toLp g
  let B : Lp ℝ ∞ μ →L[ℝ] Lp ℝ 1 μ →L[ℝ] Lp ℝ 1 μ :=
    (ContinuousLinearMap.mul ℝ ℝ).holderL μ ∞ 1 1
  have hEq : (fun f : Lp ℝ 2 μ => ∫ x, g x ∂(squareMeasure μ f : Measure α)) =
      fun f => ∫ x, (B gLp (square μ f)) x ∂μ := by
    funext f
    rw [squareMeasure_integral]
    apply integral_congr_ae
    filter_upwards [square_coe μ f, (g.memLp_top (μ := μ)).coeFn_toLp,
      (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) gLp (square μ f)]
      with x h1 h2 h3
    change f x ^ 2 * g x = ((ContinuousLinearMap.mul ℝ ℝ).holder 1 gLp (square μ f)) x
    rw [h3]
    change f x ^ 2 * g x = gLp x * (square μ f) x
    change gLp x = g x at h2
    rw [h1, h2, mul_comm]
  rw [hEq]
  exact continuous_integral.comp ((B gLp).continuous.comp (square_continuous μ))

end MeasureEquivalenceDensity
end MainProofScope14

/- Source module: HellingerTransport -/
section MainProofScope15
open MeasureTheory Filter

namespace MeasureEquivalenceHellinger

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Squared Hellinger energy calculated with a specified reference measure. -/
noncomputable def energy (μ ν ρ : Measure α) : ℝ :=
  ∫ x, (Real.sqrt (μ.rnDeriv ρ x).toReal -
    Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2 ∂ρ

theorem energy_symm (μ ν ρ : Measure α) : energy μ ν ρ = energy ν μ ρ := by
  unfold energy
  congr 1
  funext x
  ring

theorem energy_map (e : α ≃ᵐ β) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] :
    energy (μ.map e) (ν.map e) (ρ.map e) = energy μ ν ρ := by
  unfold energy
  rw [integral_map_equiv]
  apply integral_congr_ae
  filter_upwards [e.measurableEmbedding.rnDeriv_map μ ρ,
    e.measurableEmbedding.rnDeriv_map ν ρ] with x hμ hν
  rw [hμ, hν]

theorem energy_change_reference (μ ν ρ σ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    energy μ ν σ = energy μ ν ρ := by
  unfold energy
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with x hmx hnx
  simp only [Pi.mul_apply] at hmx hnx
  rw [← hmx, ← hnx, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul (ENNReal.toReal_nonneg),
    Real.sqrt_mul (ENNReal.toReal_nonneg)]
  nlinarith [Real.sq_sqrt (ENNReal.toReal_nonneg : 0 ≤ (ρ.rnDeriv σ x).toReal)]

theorem energy_fixed_reference_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    energy (μ.map e) (ν.map e) ρ = energy μ ν ρ := by
  let : SigmaFinite (μ.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ν.map e) := e.measurableEmbedding.sigmaFinite_map
  let : SigmaFinite (ρ.map e) := e.measurableEmbedding.sigmaFinite_map
  rw [energy_change_reference (μ.map e) (ν.map e) (ρ.map e) ρ
    (e.measurableEmbedding.absolutelyContinuous_map hμ)
    (e.measurableEmbedding.absolutelyContinuous_map hν) hρ]
  exact energy_map e μ ν ρ

theorem energy_reference_independent (μ ν ρ σ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hμρ : μ ≪ ρ) (hνρ : ν ≪ ρ) (hμσ : μ ≪ σ) (hνσ : ν ≪ σ) :
    energy μ ν ρ = energy μ ν σ := by
  calc
    energy μ ν ρ = energy μ ν (ρ + σ) :=
      (energy_change_reference μ ν ρ (ρ + σ) hμρ hνρ
        (Measure.AbsolutelyContinuous.rfl.add_right σ)).symm
    _ = energy μ ν σ := energy_change_reference μ ν σ (ρ + σ) hμσ hνσ
      (Measure.AbsolutelyContinuous.rfl.add_right' ρ)

theorem sqrt_rnDeriv_memLp (μ ρ : Measure α) [IsFiniteMeasure μ] :
    MemLp (fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal) 2 ρ := by
  apply (memLp_two_iff_integrable_sq
    ((Measure.measurable_rnDeriv μ ρ).ennreal_toReal.sqrt.aestronglyMeasurable)).2
  have hi := Measure.integrableOn_toReal_rnDeriv (ν := ρ) (measure_ne_top μ Set.univ)
  simpa only [IntegrableOn, Measure.restrict_univ, Real.sq_sqrt ENNReal.toReal_nonneg]
    using hi

/-- The actual L² class of the nonnegative square root of a finite measure's RN density. -/
noncomputable def root (μ ρ : Measure α) [IsFiniteMeasure μ] : Lp ℝ 2 ρ :=
  (sqrt_rnDeriv_memLp μ ρ).toLp (fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal)

theorem root_coe (μ ρ : Measure α) [IsFiniteMeasure μ] :
    root μ ρ =ᵐ[ρ] fun x ↦ Real.sqrt (μ.rnDeriv ρ x).toReal :=
  (sqrt_rnDeriv_memLp μ ρ).coeFn_toLp

theorem root_dist_sq (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    dist (root μ ρ) (root ν ρ) ^ 2 = energy μ ν ρ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  unfold energy
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (root μ ρ) (root ν ρ), root_coe μ ρ,
    root_coe ν ρ] with x hs hμ hν
  simp only [Pi.sub_apply] at hs
  rw [hs, hμ, hν]
  simp [sq]

theorem root_dist_map (e : α ≃ᵐ α) (μ ν ρ : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ.map e ≪ ρ) :
    dist (root (μ.map e) ρ) (root (ν.map e) ρ) = dist (root μ ρ) (root ν ρ) := by
  have he := energy_fixed_reference_map e μ ν ρ hμ hν hρ
  rw [← root_dist_sq, ← root_dist_sq] at he
  nlinarith [dist_nonneg (x := root (μ.map e) ρ) (y := root (ν.map e) ρ),
    dist_nonneg (x := root μ ρ) (y := root ν ρ)]

theorem root_nonnegative (μ ρ : Measure α) [IsFiniteMeasure μ] :
    0 ≤ root μ ρ := by
  apply (Lp.coeFn_nonneg _).1
  filter_upwards [root_coe μ ρ] with x hx
  rw [hx]
  exact Real.sqrt_nonneg _

theorem root_norm_sq (μ ρ : Measure α) [IsFiniteMeasure μ] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) : ‖root μ ρ‖ ^ 2 = μ.real Set.univ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def,
    ← Measure.integral_toReal_rnDeriv hμ]
  apply integral_congr_ae
  filter_upwards [root_coe μ ρ] with x hx
  rw [hx]
  simp [Real.sq_sqrt ENNReal.toReal_nonneg]

theorem root_probability_norm (μ ρ : Measure α) [IsProbabilityMeasure μ] [SigmaFinite ρ]
    (hμ : μ ≪ ρ) : ‖root μ ρ‖ = 1 := by
  have h := root_norm_sq μ ρ hμ
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one] at h
  nlinarith [norm_nonneg (root μ ρ)]

/-- Inversion preserves the actual L² density distance for two commuting
quasi-invariant measurable bijections. No Hellinger-invariance hypothesis is used. -/
theorem root_dist_inverse (e f : α ≃ᵐ α) (ρ : Measure α) [IsFiniteMeasure ρ]
    (hcomm : Function.Commute e f)
    (he : ρ.map e ≪ ρ) (hf : ρ.map f ≪ ρ)
    (hei : ρ.map e.symm ≪ ρ) (hfi : ρ.map f.symm ≪ ρ) :
    dist (root (ρ.map e.symm) ρ) (root (ρ.map f.symm) ρ) =
      dist (root (ρ.map e) ρ) (root (ρ.map f) ρ) := by
  have ht : ρ.map (e.trans f) ≪ ρ := by
    have ht' := (f.measurableEmbedding.absolutelyContinuous_map he).trans hf
    simpa only [Measure.map_map f.measurable e.measurable,
      MeasurableEquiv.coe_trans] using ht'
  have hmap1 : (ρ.map e.symm).map (e.trans f) = ρ.map f := by
    rw [Measure.map_map (e.trans f).measurable e.symm.measurable]
    congr 1
    funext x
    simp
  have hmap2 : (ρ.map f.symm).map (e.trans f) = ρ.map e := by
    rw [Measure.map_map (e.trans f).measurable f.symm.measurable]
    congr 1
    funext x
    change f (e (f.symm x)) = e x
    rw [← hcomm (f.symm x), f.apply_symm_apply]
  have hd := root_dist_map (e.trans f) (ρ.map e.symm) (ρ.map f.symm) ρ hei hfi ht
  simp only [hmap1, hmap2] at hd
  exact hd.symm.trans (dist_comm _ _)

end MeasureEquivalenceHellinger
end MainProofScope15

/- Source module: DensityGraphCompleteness -/
section MainProofScope16
/-!
# Abstract density-graph completeness

This verifies the inverse-sequence / closed-graph argument with explicit
analytical interface hypotheses. It does not construct square-root RN densities
or verify those analytical interface hypotheses for L2 measures.
-/

open Filter Set
open scoped Topology

namespace MeasureEquivalenceDensityGraph

variable {K V P : Type*} [Group K] [MetricSpace K] [IsTopologicalGroup K]
  [MetricSpace V] [CompleteSpace V] [TopologicalSpace P] [T2Space P]

/-- Closedness of the feature graph. The predicate `A` models one-sided
absolute continuity; `ν` models a density-to-measure map. -/
theorem isClosed_density_graph (H : Subgroup K) (r : H → V)
    (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    IsClosed (Set.range (fun h : H => ((h : K), r h))) := by
  have limit_identity {u : ℕ → H} {g : K} {v : V}
      (hu : Tendsto (fun n => (u n : K)) atTop (𝓝 g))
      (hv : Tendsto (fun n => r (u n)) atTop (𝓝 v)) : μ g = ν v := by
    have hp := hμ.continuousAt.tendsto.comp hu
    have hq := hν.continuousAt.tendsto.comp hv
    exact tendsto_nhds_unique hp (by simpa only [Function.comp_def, hfactor] using hq)
  apply isSeqClosed_iff_isClosed.mp
  intro s p hs hp
  choose u hu using hs
  have hlim : Tendsto (fun n => ((u n : K), r (u n))) atTop (𝓝 p) := by
    simpa only [hu] using hp
  have hK := (continuous_fst.tendsto p).comp hlim
  have hV := (continuous_snd.tendsto p).comp hlim
  have hforward : μ p.1 = ν p.2 := limit_identity hK hV
  have hC : CauchySeq (fun n => r ((u n)⁻¹)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hV.cauchySeq ε hε
    exact ⟨N, fun i hi j hj => by rw [hinv]; exact hN i hi j hj⟩
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hC
  have hKinv : Tendsto (fun n => (((u n)⁻¹ : H) : K)) atTop (𝓝 p.1⁻¹) := by
    simpa only [Subgroup.coe_inv, Function.comp_def] using hK.inv
  have hback : μ p.1⁻¹ = ν w := limit_identity hKinv hw
  have hpH : p.1 ∈ H := (hH p.1).mpr ⟨hforward.symm ▸ hA p.2, hback.symm ▸ hA w⟩
  refine ⟨⟨p.1, hpH⟩, ?_⟩
  apply Prod.ext
  · rfl
  · apply hνinj
    exact (hfactor ⟨p.1, hpH⟩).trans hforward

/-- Completeness uses only completeness of the ambient parameter metric;
compactness is not required by this abstract result. -/
theorem isComplete_density_graph [CompleteSpace K]
    (H : Subgroup K) (r : H → V) (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    IsComplete (Set.range (fun h : H => ((h : K), r h))) :=
  (isClosed_density_graph H r μ ν A hμ hν hνinj hfactor hA hH hinv).isComplete

/-- The graph equipped with the inherited product metric is a complete metric
space. Pullback to `H` is obtained via its bijective graph parametrization. -/
theorem completeSpace_density_graph [CompleteSpace K]
    (H : Subgroup K) (r : H → V) (μ : K → P) (ν : V → P) (A : P → Prop)
    (hμ : Continuous μ) (hν : Continuous ν) (hνinj : Function.Injective ν)
    (hfactor : ∀ h : H, ν (r h) = μ (h : K))
    (hA : ∀ v : V, A (ν v))
    (hH : ∀ g : K, g ∈ H ↔ A (μ g) ∧ A (μ g⁻¹))
    (hinv : ∀ h k : H, dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k)) :
    CompleteSpace (Set.range (fun h : H => ((h : K), r h))) :=
  (isComplete_density_graph H r μ ν A hμ hν hνinj hfactor hA hH hinv).completeSpace_coe

end MeasureEquivalenceDensityGraph

namespace MeasureEquivalenceInverseAC

open MeasureTheory

/-- The measure-specific inverse step: one-sided AC of the inverse translate
gives the opposite AC direction after pushing forward by the bijection. -/
theorem inverse_pushforward_ac {Z : Type*} [MeasurableSpace Z]
    (M : Measure Z) (T : Z ≃ᵐ Z) (h : M.map T.symm ≪ M) :
    M ≪ M.map T := by
  have hmap := T.measurableEmbedding.absolutelyContinuous_map h
  simpa only [MeasurableEquiv.map_map_symm] using hmap

/-- Mutual absolute continuity can therefore be tested using forward and
inverse one-sided absolute continuity. -/
theorem mutual_ac_iff_forward_inverse {Z : Type*} [MeasurableSpace Z]
    (M : Measure Z) (T : Z ≃ᵐ Z) :
    (M.map T ≪ M ∧ M ≪ M.map T) ↔
      (M.map T ≪ M ∧ M.map T.symm ≪ M) := by
  constructor
  · rintro ⟨hf, hb⟩
    refine ⟨hf, ?_⟩
    have hmap := T.symm.measurableEmbedding.absolutelyContinuous_map hb
    simpa only [MeasurableEquiv.map_symm_map] using hmap
  · rintro ⟨hf, hi⟩
    exact ⟨hf, inverse_pushforward_ac M T hi⟩

end MeasureEquivalenceInverseAC
end MainProofScope16

/- Source module: PolishGroupTopology -/
section MainProofScope17
/-!
Pettis category, Borel-homomorphism continuity, and uniqueness of compatible
Polish group topologies. This is a new standalone verification development.
-/

open Filter Set TopologicalSpace
open scoped Topology Pointwise

namespace MeasureEquivalenceTopology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BaireSpace G]

/-- Pettis's category lemma, proved from the property of Baire. -/
theorem pettis_nhds_one {A : Set G} (hA : BaireMeasurableSet A)
    (hnot : ¬ IsMeagre A) : A / A ∈ 𝓝 (1 : G) := by
  obtain ⟨U, hU, hAU⟩ := hA.residualEq_isOpen
  have hprop : ∀ᵇ x, x ∈ A ↔ x ∈ U := Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra h
    have hzero : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    apply hnot
    change Aᶜ ∈ residual G
    filter_upwards [hprop] with x hx
    intro hxA
    have hxU := hx.mp hxA
    simp [hzero] at hxU
  obtain ⟨u, hu⟩ := hUne
  let W : Set G := {g | g⁻¹ * u ∈ U}
  have hW : W ∈ 𝓝 (1 : G) := by
    apply (hU.preimage (by fun_prop : Continuous (fun g : G => g⁻¹ * u))).mem_nhds
    simpa using hu
  apply Filter.mem_of_superset hW
  intro g hg
  have htrans : ∀ᵇ x, g⁻¹ * x ∈ A ↔ g⁻¹ * x ∈ U :=
    (tendsto_residual_of_isOpenMap
      (by fun_prop : Continuous (fun x : G => g⁻¹ * x))
      (isOpenMap_mul_left g⁻¹)) hprop
  let B : Set G := U ∩ (fun x : G => g⁻¹ * x) ⁻¹' U
  have hB : IsOpen B := hU.inter (hU.preimage (by fun_prop))
  have hBne : B.Nonempty := ⟨u, hu, hg⟩
  have hd : Dense {x : G | (x ∈ A ↔ x ∈ U) ∧
      (g⁻¹ * x ∈ A ↔ g⁻¹ * x ∈ U)} :=
    dense_of_mem_residual (hprop.and htrans)
  obtain ⟨x, hxB, hxR⟩ := hd.inter_open_nonempty B hB hBne
  refine Set.mem_div.mpr ⟨x, hxR.1.mpr hxB.1, g⁻¹ * x, hxR.2.mpr hxB.2, ?_⟩
  simp [div_eq_mul_inv]

/-- A Borel homomorphism from a Baire topological group to a second-countable
topological group is continuous. Neither surjectivity nor Polishness is needed. -/
theorem continuous_borel_hom [MeasurableSpace G] [BorelSpace G]
    {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [SecondCountableTopology L] [MeasurableSpace L] [BorelSpace L]
    (f : G →* L) (hf : Measurable f) : Continuous f := by
  apply continuous_of_tendsto_nhds_one f
  intro U hU
  obtain ⟨V, hV, hVV⟩ := exists_nhds_split_inv hU
  obtain ⟨W, hWV, hWopen, hWone⟩ := mem_nhds_iff.mp hV
  let C : L → Set L := fun y => {z | z / y ∈ W}
  have hCopen (y : L) : IsOpen (C y) :=
    hWopen.preimage (by fun_prop : Continuous (fun z : L => z / y))
  have hCnhds (y : L) : C y ∈ 𝓝 y := (hCopen y).mem_nhds (by simpa [C])
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hCnhds
  have hcover : (⋃ y ∈ S, f ⁻¹' C y) = (Set.univ : Set G) := by
    have hpre := congrArg (fun T : Set L => f ⁻¹' T) hScover
    simpa only [Set.preimage_iUnion, Set.preimage_univ] using hpre
  have hnon : ∃ y ∈ S, ¬ IsMeagre (f ⁻¹' C y) := by
    by_contra h
    push Not at h
    have hmeagre := isMeagre_biUnion hScount h
    rw [hcover] at hmeagre
    exact not_isMeagre_of_isOpen isOpen_univ Set.univ_nonempty hmeagre
  obtain ⟨y, _hyS, hy⟩ := hnon
  have hBP : BaireMeasurableSet (f ⁻¹' C y) :=
    (hf (hCopen y).measurableSet).baireMeasurableSet
  apply Filter.mem_of_superset (pettis_nhds_one hBP hy)
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_div.mp hz
  change f (a / b) ∈ U
  have haV : f a / y ∈ V := hWV ha
  have hbV : f b / y ∈ V := hWV hb
  have hh := hVV (f a / y) haV (f b / y) hbV
  simpa only [map_div, div_div_div_cancel_right] using hh

section Polish

variable [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
  {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [PolishSpace L] [MeasurableSpace L] [BorelSpace L]

/-- A Borel group isomorphism between Polish groups has Borel inverse by
Lusin--Souslin, and both directions are continuous by the category argument. -/
def borelGroupIsoHomeomorph (e : G ≃* L) (he : Measurable e) : G ≃ₜ L where
  toEquiv := e.toEquiv
  continuous_toFun := continuous_borel_hom e.toMonoidHom he
  continuous_invFun := by
    apply continuous_borel_hom e.symm.toMonoidHom
    apply (he.measurableEmbedding e.injective).measurable_comp_iff.mp
    change Measurable (fun x : L => e (e.symm x))
    have heq : (fun x : L => e (e.symm x)) = id := funext e.apply_symm_apply
    rw [heq]
    exact measurable_id

/-- Two Polish group presentations with the same continuous injective image
have the same topology under their algebraic identification. -/
def inclusionGroupIsoHomeomorph {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (i : G → X) (j : L → X) (hi : Continuous i) (hj : Continuous j)
    (hjinj : Function.Injective j) (e : G ≃* L) (he : ∀ x, j (e x) = i x) : G ≃ₜ L := by
  apply borelGroupIsoHomeomorph e
  apply (hj.measurableEmbedding hjinj).measurable_comp_iff.mp
  simpa only [Function.comp_def, he] using hi.measurable

end Polish

end MeasureEquivalenceTopology
end MainProofScope17

/- Source module: RNGraph -/
section MainProofScope18
open MeasureTheory Filter Set
open scoped Topology

namespace MeasureEquivalenceRNGraph

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z]

theorem squareMeasure_root (M ν : Measure Z) [SigmaFinite M] [IsFiniteMeasure ν]
    (hν : ν ≪ M) : (squareMeasure M (root ν M) : Measure Z) = ν := by
  change M.withDensity (fun x => ENNReal.ofReal ((root ν M) x ^ 2)) = ν
  calc
    _ = M.withDensity (ν.rnDeriv M) := by
      apply withDensity_congr_ae
      filter_upwards [root_coe ν M, Measure.rnDeriv_ne_top ν M] with x hx htop
      rw [hx, Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal htop]
    _ = ν := Measure.withDensity_rnDeriv_eq ν M hν

section Action

variable {K : Type*} [CommGroup K] [TopologicalSpace K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]

noncomputable def orbit (g : K) : FiniteMeasure Z :=
  ⟨M.map (fun z => g • z), inferInstance⟩

instance orbit_isProbability (g : K) : IsProbabilityMeasure (orbit M g : Measure Z) := by
  change IsProbabilityMeasure (M.map (fun z => g • z))
  exact M.isProbabilityMeasure_map (measurable_const_smul g).aemeasurable

theorem orbit_continuous [FirstCountableTopology K] : Continuous (orbit (K := K) M) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hrep : (fun g : K => ∫ z, f z ∂(orbit M g : Measure Z)) =
      fun g : K => ∫ z, f (g • z) ∂M := by
    funext g
    exact integral_map_equiv (MeasurableEquiv.smul g) f
  rw [hrep]
  apply continuous_of_dominated (bound := fun _ => ‖f‖)
  · intro g
    exact (f.continuous.comp (continuous_const_smul g)).aestronglyMeasurable
  · intro g
    exact Filter.Eventually.of_forall (fun z => f.norm_coe_le_norm (g • z))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun z => f.continuous.comp (continuous_id.smul continuous_const))

omit [IsProbabilityMeasure M] in
theorem map_orbit (g h : K) :
    (M.map (fun z => h • z)).map (fun z => g • z) = M.map (fun z => (g * h) • z) := by
  rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
  congr 1
  funext z
  exact (mul_smul g h z).symm

/-- Exact quasi-invariance subgroup, tested by forward and inverse one-sided AC. -/
def quasiInvariantSubgroup : Subgroup K where
  carrier := {g | M.map (fun z => g • z) ≪ M ∧ M.map (fun z => g⁻¹ • z) ≪ M}
  one_mem' := by simpa using (And.intro (Measure.AbsolutelyContinuous.refl M) (Measure.AbsolutelyContinuous.refl M))
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [← map_orbit M g h]
      exact ((MeasurableEquiv.smul g).measurableEmbedding.absolutelyContinuous_map hh.1).trans hg.1
    · rw [mul_inv_rev, ← map_orbit M h⁻¹ g⁻¹]
      exact ((MeasurableEquiv.smul h⁻¹).measurableEmbedding.absolutelyContinuous_map hg.2).trans hh.2
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩

omit [IsProbabilityMeasure M] in
theorem mem_quasiInvariantSubgroup_iff (g : K) :
    g ∈ quasiInvariantSubgroup (K := K) M ↔
      M.map (fun z => g • z) ≪ M ∧ M ≪ M.map (fun z => g • z) := by
  exact (MeasureEquivalenceInverseAC.mutual_ac_iff_forward_inverse M
    (MeasurableEquiv.smul g)).symm

noncomputable def feature (h : quasiInvariantSubgroup (K := K) M) : positiveUnitSphere M :=
  ⟨root (orbit M (h : K) : Measure Z) M,
    root_nonnegative _ _, root_probability_norm _ _ h.property.1⟩

theorem feature_factor (h : quasiInvariantSubgroup (K := K) M) :
    squareMeasure M (feature M h : Lp ℝ 2 M) = orbit M (h : K) := by
  apply Subtype.ext
  exact squareMeasure_root M _ h.property.1

theorem feature_inverse (h k : quasiInvariantSubgroup (K := K) M) :
    dist (feature M h⁻¹) (feature M k⁻¹) = dist (feature M h) (feature M k) := by
  apply root_dist_inverse (MeasurableEquiv.smul (h : K)) (MeasurableEquiv.smul (k : K)) M
  · intro z
    exact smul_comm (h : K) (k : K) z
  · exact h.property.1
  · exact k.property.1
  · exact h.property.2
  · exact k.property.2

theorem feature_mul_left (a h k : quasiInvariantSubgroup (K := K) M) :
    dist (feature M (a * h)) (feature M (a * k)) = dist (feature M h) (feature M k) := by
  have hd := root_dist_map (MeasurableEquiv.smul (a : K))
    (orbit M (h : K) : Measure Z) (orbit M (k : K) : Measure Z) M
    h.property.1 k.property.1 a.property.1
  change dist (root ((M.map (fun z => (h : K) • z)).map (fun z => (a : K) • z)) M)
    (root ((M.map (fun z => (k : K) • z)).map (fun z => (a : K) • z)) M) =
    dist (root (M.map (fun z => (h : K) • z)) M)
      (root (M.map (fun z => (k : K) • z)) M) at hd
  simp only [map_orbit] at hd
  exact hd

end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]

noncomputable def graphMap (h : quasiInvariantSubgroup (K := K) M) :
    K × positiveUnitSphere M := ((h : K), feature M h)

theorem isClosed_graph : IsClosed (Set.range (graphMap (K := K) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  apply MeasureEquivalenceDensityGraph.isClosed_density_graph
    (quasiInvariantSubgroup M) (feature M) (orbit M)
    (fun v : positiveUnitSphere M => squareMeasure M v)
    (fun ν : FiniteMeasure Z => (ν : Measure Z) ≪ M)
  · exact orbit_continuous M
  · exact (squareMeasure_continuous M).comp continuous_subtype_val
  · intro v w hvw
    apply Subtype.ext
    exact squareMeasure_injective_nonnegative M v.property.1 w.property.1 hvw
  · exact feature_factor M
  · intro v
    exact squareMeasure_ac M v
  · intro g
    rfl
  · exact feature_inverse M

theorem isComplete_graph [CompleteSpace K] :
    IsComplete (Set.range (graphMap (K := K) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  exact (isClosed_graph M).isComplete

theorem completeSpace_graph [CompleteSpace K] :
    CompleteSpace (Set.range (graphMap (K := K) M)) :=
  (isComplete_graph M).completeSpace_coe

end Graph

end MeasureEquivalenceRNGraph
end MainProofScope18

/- Source module: InvariantGraphGroup -/
section MainProofScope19
open Set
open scoped Topology

namespace MeasureEquivalenceInvariantGraph

variable {K V : Type*} [CommGroup K] [MetricSpace K]
    [MetricSpace V] (H : Subgroup K) (r : H → V)

/-- A separate presentation of H, carrying the graph metric rather than its
possibly incomplete subspace metric from K. -/
def GraphGroup (_r : H → V) : Type _ := H

instance : CommGroup (GraphGroup H r) := inferInstanceAs (CommGroup H)

def inclusion (h : GraphGroup H r) : K := (show H from h)

def graph (h : GraphGroup H r) : K × V := (inclusion H r h, r h)

omit [MetricSpace K] [MetricSpace V] in
theorem inclusion_injective : Function.Injective (inclusion H r) := by
  intro a b hab
  exact Subtype.ext hab

omit [MetricSpace K] [MetricSpace V] in
theorem graph_injective : Function.Injective (graph H r) := by
  intro a b hab
  exact inclusion_injective H r (congrArg Prod.fst hab)

noncomputable instance : MetricSpace (GraphGroup H r) :=
  MetricSpace.induced (graph H r) (graph_injective H r) inferInstance

theorem graph_isometry : Isometry (graph H r) := Isometry.of_dist_eq (fun _ _ => rfl)

theorem inclusion_continuous : Continuous (inclusion H r) :=
  continuous_fst.comp (graph_isometry H r).continuous

theorem feature_continuous : Continuous (fun h : GraphGroup H r => r h) :=
  continuous_snd.comp (graph_isometry H r).continuous

theorem feature_dist_le (a b : GraphGroup H r) : dist (r a) (r b) ≤ dist a b := by
  change dist (r a) (r b) ≤ max (dist (inclusion H r a) (inclusion H r b)) (dist (r a) (r b))
  exact le_max_right _ _

variable (hleft : ∀ a h k : H, dist (r (a * h)) (r (a * k)) = dist (r h) (r k))

include hleft in
omit [MetricSpace K] in
theorem feature_inverse (h k : H) : dist (r h⁻¹) (r k⁻¹) = dist (r h) (r k) := by
  have hi := hleft (h * k) h⁻¹ k⁻¹
  have hh : h * k * h⁻¹ = k := by simp
  have hk : h * k * k⁻¹ = h := by group
  rw [hh, hk] at hi
  exact hi.symm.trans (dist_comm _ _)

include hleft in
omit [MetricSpace K] in
theorem feature_mul_bound (a b c d : H) :
    dist (r (a * b)) (r (c * d)) ≤ dist (r a) (r c) + dist (r b) (r d) := by
  calc
    _ ≤ dist (r (a * b)) (r (c * b)) + dist (r (c * b)) (r (c * d)) := dist_triangle _ _ _
    _ = _ := by rw [hleft, mul_comm a b, mul_comm c b, hleft]

include hleft in
theorem graphGroup_topologicalGroup [IsTopologicalGroup K] : IsTopologicalGroup (GraphGroup H r) where
  continuous_mul := by
    apply (graph_isometry H r).isEmbedding.continuous_iff.mpr
    have hr : LipschitzWith 2 (fun p : GraphGroup H r × GraphGroup H r => r (p.1 * p.2)) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      have hb := feature_mul_bound H r hleft p.1 p.2 q.1 q.2
      have h1 := feature_dist_le H r p.1 q.1
      have h2 := feature_dist_le H r p.2 q.2
      have h3 := le_max_left (dist p.1 q.1) (dist p.2 q.2)
      have h4 := le_max_right (dist p.1 q.1) (dist p.2 q.2)
      simp only [NNReal.coe_ofNat, Prod.dist_eq]
      exact hb.trans ((add_le_add h1 h2).trans (by linarith))
    exact (((inclusion_continuous H r).comp continuous_fst).mul
      ((inclusion_continuous H r).comp continuous_snd)).prodMk hr.continuous
  continuous_inv := by
    apply (graph_isometry H r).isEmbedding.continuous_iff.mpr
    have hr : LipschitzWith 1 (fun p : GraphGroup H r => r p⁻¹) := by
      apply LipschitzWith.of_dist_le_mul
      intro p q
      simp only [NNReal.coe_one, one_mul]
      exact (feature_inverse H r hleft p q).le.trans (feature_dist_le H r p q)
    exact (inclusion_continuous H r).inv.prodMk hr.continuous

theorem graphGroup_complete [CompleteSpace K] [CompleteSpace V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h)))) :
    CompleteSpace (GraphGroup H r) := by
  let : CompleteSpace (Set.range (graph H r)) := hclosed.isComplete.completeSpace_coe
  exact (graph_isometry H r).isometryEquivOnRange.completeSpace

theorem graphGroup_secondCountable [SecondCountableTopology K] [SecondCountableTopology V] :
    SecondCountableTopology (GraphGroup H r) :=
  TopologicalSpace.secondCountableTopology_induced (GraphGroup H r) (K × V) (graph H r)

theorem graphGroup_polish [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h)))) :
    PolishSpace (GraphGroup H r) := by
  let : CompleteSpace (GraphGroup H r) := graphGroup_complete H r hclosed
  let : SecondCountableTopology (GraphGroup H r) := graphGroup_secondCountable H r
  infer_instance

section Presentation

variable [IsTopologicalGroup K] [CompleteSpace K] [CompleteSpace V]
    [SecondCountableTopology K] [SecondCountableTopology V]
    (hclosed : IsClosed (Set.range (fun h : H => ((h : K), r h))))
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

include hleft hclosed in
/-- The algebraic identification with any Polish group presentation whose
coordinate inclusion is continuous is a homeomorphism onto the graph group. -/
noncomputable def presentationHomeomorph (e : G ≃* H)
    (he : Continuous (fun g : G => (e g : K))) : G ≃ₜ GraphGroup H r := by
  let : IsTopologicalGroup (GraphGroup H r) := graphGroup_topologicalGroup H r hleft
  let : PolishSpace (GraphGroup H r) := graphGroup_polish H r hclosed
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let : MeasurableSpace (GraphGroup H r) := borel (GraphGroup H r)
  let : BorelSpace (GraphGroup H r) := ⟨rfl⟩
  let e' : G ≃* GraphGroup H r := e
  exact MeasureEquivalenceTopology.inclusionGroupIsoHomeomorph
    (fun g : G => (e g : K)) (inclusion H r) he (inclusion_continuous H r)
    (inclusion_injective H r) e' (fun _ => rfl)

include hleft hclosed in
theorem presentation_graph_embedding (e : G ≃* H)
    (he : Continuous (fun g : G => (e g : K))) :
    Topology.IsEmbedding (fun g : G => ((e g : K), r (e g))) := by
  exact (graph_isometry H r).isEmbedding.comp
    (presentationHomeomorph H r hleft hclosed e he).isEmbedding

end Presentation

end MeasureEquivalenceInvariantGraph
end MainProofScope19

/- Source module: RNPresentation -/
section MainProofScope20
open MeasureTheory Set
open scoped Topology ENNReal

namespace MeasureEquivalenceRNPresentation

open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph

variable {K Z G : Type*}
    [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [CompleteSpace K] [SecondCountableTopology K]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]

theorem rn_graph_embedding_equiv (e : G ≃* quasiInvariantSubgroup (K := K) M)
    (he : Continuous (fun g : G => (e g : K))) :
    Topology.IsEmbedding (fun g : G =>
      ((e g : K), root (orbit M (e g : K) : Measure Z) M)) := by
  let : CompleteSpace (positiveUnitSphere M) := positiveUnitSphere_complete M
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  have hgraph := presentation_graph_embedding
    (quasiInvariantSubgroup M) (feature M) (feature_mul_left M) (isClosed_graph M) e he
  have hsub : Topology.IsEmbedding (fun p : K × positiveUnitSphere M =>
      (p.1, (p.2 : Lp ℝ 2 M))) :=
    Topology.IsEmbedding.id.prodMap Topology.IsEmbedding.subtypeVal
  exact hsub.comp hgraph

/-- A continuous injective homomorphism whose image is exactly the
quasi-invariance subgroup has an embedded actual RN square-root graph.
No continuity or Borel hypothesis on the root feature is assumed. -/
theorem rn_graph_embedding (i : G →* K) (hi : Continuous i)
    (hinj : Function.Injective i)
    (hrange : Set.range i = (quasiInvariantSubgroup (K := K) M : Set K)) :
    Topology.IsEmbedding (fun g : G =>
      (i g, root (orbit M (i g) : Measure Z) M)) := by
  have hmem (g : G) : i g ∈ quasiInvariantSubgroup (K := K) M := by
    change i g ∈ (quasiInvariantSubgroup (K := K) M : Set K)
    rw [← hrange]
    exact Set.mem_range_self g
  let j : G →* quasiInvariantSubgroup (K := K) M := i.codRestrict _ hmem
  have hjinj : Function.Injective j := by
    intro x y hxy
    exact hinj (congrArg Subtype.val hxy)
  have hjsurj : Function.Surjective j := by
    intro h
    have hh : (h : K) ∈ Set.range i := hrange.symm ▸ h.property
    obtain ⟨g, hg⟩ := hh
    exact ⟨g, Subtype.ext hg⟩
  let e : G ≃* quasiInvariantSubgroup (K := K) M := MulEquiv.ofBijective j ⟨hjinj, hjsurj⟩
  have he (g : G) : (e g : K) = i g := rfl
  have hecont : Continuous (fun g : G => (e g : K)) := by simpa only [he] using hi
  simpa only [he] using rn_graph_embedding_equiv M e hecont

omit [IsTopologicalGroup K] [CompleteSpace K] [SecondCountableTopology K]
    [PolishSpace Z] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G] in
theorem rn_distance_invariant (i : G →* K)
    (hrange : Set.range i = (quasiInvariantSubgroup (K := K) M : Set K))
    (a h k : G) :
    dist (root (orbit M (i (a * h)) : Measure Z) M)
      (root (orbit M (i (a * k)) : Measure Z) M) =
    dist (root (orbit M (i h) : Measure Z) M)
      (root (orbit M (i k) : Measure Z) M) := by
  have hmem (g : G) : i g ∈ quasiInvariantSubgroup (K := K) M := by
    change i g ∈ (quasiInvariantSubgroup (K := K) M : Set K)
    rw [← hrange]
    exact Set.mem_range_self g
  have hd := feature_mul_left M ⟨i a, hmem a⟩ ⟨i h, hmem h⟩ ⟨i k, hmem k⟩
  change dist (root (orbit M (i a * i h) : Measure Z) M)
    (root (orbit M (i a * i k) : Measure Z) M) =
    dist (root (orbit M (i h) : Measure Z) M)
      (root (orbit M (i k) : Measure Z) M) at hd
  simpa only [map_mul] using hd

end MeasureEquivalenceRNPresentation
end MainProofScope20

/- Source module: FiniteFourier -/
section MainProofScope21
/-!
Finite Hilbert-valued Fourier identities for the finite-torus feasibility check.
This file is a separate development and does not alter the earlier checks.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceFourier

variable {G E : Type*} [AddCommGroup G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma character_orthogonality_sum (χ ψ : AddChar G ℂ) :
    (∑ x, conj (χ x) * ψ x) =
      if χ = ψ then (Fintype.card G : ℂ) else 0 := by
  classical
  have h := AddChar.wInner_cWeight_eq_boole χ ψ
  simp only [RCLike.wInner_cWeight_eq_expect, RCLike.inner_apply,
    Fintype.expect_eq_sum_div_card] at h
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  split_ifs with heq
  · simp only [heq, ite_true] at h
    have hh := (div_eq_iff hc).mp h
    simpa [heq, mul_comm] using hh
  · simp only [heq, ite_false] at h
    have hh := (div_eq_iff hc).mp h
    simpa [mul_comm] using hh

lemma synthesis_inner (v w : AddChar G ℂ → E) :
    (∑ x, inner ℂ (∑ χ : AddChar G ℂ, χ x • v χ)
      (∑ ψ : AddChar G ℂ, ψ x • w ψ)) =
      (Fintype.card G : ℂ) * ∑ χ : AddChar G ℂ, inner ℂ (v χ) (w χ) := by
  classical
  simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  calc
    (∑ x, ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
        conj (χ x) * (ψ x * inner ℂ (v χ) (w ψ))) =
        ∑ χ : AddChar G ℂ, ∑ ψ : AddChar G ℂ,
          (∑ x, conj (χ x) * ψ x) * inner ℂ (v χ) (w ψ) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ψ _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (Fintype.card G : ℂ) *
        ∑ χ : AddChar G ℂ, inner ℂ (v χ) (w χ) := by
      simp_rw [character_orthogonality_sum]
      simp [Finset.mul_sum]

theorem synthesis_parseval (v : AddChar G ℂ → E) :
    (∑ x, ‖∑ χ : AddChar G ℂ, χ x • v χ‖ ^ 2) =
      (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ, ‖v χ‖ ^ 2 := by
  have h := synthesis_inner v v
  simp only [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

noncomputable def coefficient (F : G → E) (χ : AddChar G ℂ) : E :=
  (Fintype.card G : ℂ)⁻¹ • ∑ y, conj (χ y) • F y

theorem inversion (F : G → E) (x : G) :
    (∑ χ : AddChar G ℂ, χ x • coefficient F χ) = F x := by
  classical
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hχ (χ : AddChar G ℂ) (y : G) :
      χ x * conj (χ y) = χ (x - y) := by
    rw [χ.map_sub_eq_div, div_eq_mul_inv, χ.inv_apply_eq_conj]
  calc
    (∑ χ : AddChar G ℂ, χ x • coefficient F χ) =
        (Fintype.card G : ℂ)⁻¹ • ∑ y,
          (∑ χ : AddChar G ℂ, χ (x - y)) • F y := by
      simp only [coefficient, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro χ _
      rw [← hχ]
      congr 1
      ring
    _ = (Fintype.card G : ℂ)⁻¹ • ((Fintype.card G : ℂ) • F x) := by
      simp [AddChar.sum_apply_eq_ite, sub_eq_zero]
    _ = F x := by simp [smul_smul, hc]

theorem translation_energy (F : G → E) (a : G) :
    (∑ x, ‖F (x + a) - F x‖ ^ 2) =
      (Fintype.card G : ℝ) *
        ∑ χ : AddChar G ℂ, ‖χ a - 1‖ ^ 2 * ‖coefficient F χ‖ ^ 2 := by
  have hpoint (x : G) : F (x + a) - F x =
      ∑ χ : AddChar G ℂ, χ x • ((χ a - 1) • coefficient F χ) := by
    rw [← inversion F (x + a), ← inversion F x, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro χ _
    rw [χ.map_add_eq_mul, mul_smul, sub_smul, one_smul, smul_sub]
  simp_rw [hpoint]
  rw [synthesis_parseval]
  simp [norm_smul, mul_pow]

lemma translation_family_energy {K : Type*} [Fintype K] (c : K → G) (F : G → E) :
      (∑ i, ∑ x, ‖F (x + c i) - F x‖ ^ 2) =
        (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
          (∑ i, ‖χ (c i) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 := by
  simp_rw [translation_energy]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_mul]

/-- A comparison of scalar Fourier multipliers gives the same comparison
for every function with values in a complex inner product space. -/
theorem spectral_comparison {I J : Type*} [Fintype I] [Fintype J]
    (a : I → G) (b : J → G) (C : ℝ)
    (hmult : ∀ χ : AddChar G ℂ,
      (∑ i, ‖χ (a i) - 1‖ ^ 2) ≤ C * ∑ j, ‖χ (b j) - 1‖ ^ 2)
    (F : G → E) :
    (∑ i, ∑ x, ‖F (x + a i) - F x‖ ^ 2) ≤
      C * ∑ j, ∑ x, ‖F (x + b j) - F x‖ ^ 2 := by
  rw [translation_family_energy a F, translation_family_energy b F]
  calc
    (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
        (∑ i, ‖χ (a i) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 ≤
        (Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
          (C * ∑ j, ‖χ (b j) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun χ _ =>
        mul_le_mul_of_nonneg_right (hmult χ) (sq_nonneg _)
    _ = C * ((Fintype.card G : ℝ) * ∑ χ : AddChar G ℂ,
        (∑ j, ‖χ (b j) - 1‖ ^ 2) * ‖coefficient F χ‖ ^ 2) := by
      simp_rw [mul_assoc, ← Finset.mul_sum]
      ring

end MeasureEquivalenceFourier
end MainProofScope21

/- Source module: ScalarMultiplier -/
section MainProofScope22
/-!
# Scalar finite-product estimate

This file verifies only an elementary scalar estimate used in a Fourier argument.
It does not formalize Parseval's identity, the trigonometric multiplier bound,
or any theorem about Borel reducibility or equivalence of measures.
-/

open scoped BigOperators

namespace MeasureEquivalenceScalar

/-- A reciprocal form of Bernoulli's inequality, proved by induction. -/
theorem reciprocal_bernoulli (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ) :
    (1 + (n : ℝ) * a) * (1 - a) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 ≤ (1 - a) ^ n := pow_nonneg (sub_nonneg.mpr ha1) _
    calc
      (1 + ((n + 1 : ℕ) : ℝ) * a) * (1 - a) ^ (n + 1) =
          ((1 + (n : ℝ) * a) - ((n : ℝ) + 1) * a ^ 2) * (1 - a) ^ n := by
            push_cast
            rw [pow_succ]
            ring
      _ ≤ (1 + (n : ℝ) * a) * (1 - a) ^ n := by
        apply mul_le_mul_of_nonneg_right _ hp
        have hsq : 0 ≤ ((n : ℝ) + 1) * a ^ 2 := by positivity
        linarith
      _ ≤ 1 := ih

/-- The quantitative loss in a power, valid when the total loss is at most one. -/
theorem power_loss (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (hna : (n : ℝ) * a ≤ 1) :
    (1 - a) ^ n ≤ 1 - (n : ℝ) * a / 2 := by
  have hx0 : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
  have hx2 : ((n : ℝ) * a) ^ 2 ≤ (n : ℝ) * a := by nlinarith
  have hden : 0 < 1 + (n : ℝ) * a := by positivity
  apply (mul_le_mul_iff_right₀ hden).mp
  calc
    (1 + (n : ℝ) * a) * (1 - a) ^ n ≤ 1 := reciprocal_bernoulli a ha ha1 n
    _ ≤ (1 + (n : ℝ) * a) * (1 - (n : ℝ) * a / 2) := by nlinarith

/--
If every scalar has absolute value at most one and `t.card` marked scalars
have absolute value at most `1-a`, the product loses at least `t.card*a/2`.
The factors may be negative, and both finite sets may be empty.
-/
theorem finite_product_loss {ι : Type*} (s t : Finset ι) (q : ι → ℝ) (a : ℝ)
    (hts : t ⊆ s) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hq : ∀ i ∈ s, |q i| ≤ 1)
    (hmarked : ∀ i ∈ t, |q i| ≤ 1 - a)
    (hra : (t.card : ℝ) * a ≤ 1) :
    (t.card : ℝ) * a / 2 ≤ 1 - ∏ i ∈ s, q i := by
  have hprod : (∏ i ∈ s, q i) ≤ (1 - a) ^ t.card := by
    calc
      (∏ i ∈ s, q i) ≤ |∏ i ∈ s, q i| := le_abs_self _
      _ = ∏ i ∈ s, |q i| := Finset.abs_prod s q
      _ ≤ ∏ i ∈ t, |q i| :=
        Finset.prod_le_prod_of_subset_of_le_one hts
          (fun i _ => abs_nonneg (q i)) (fun i hi _ => hq i hi)
      _ ≤ ∏ _i ∈ t, (1 - a) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg (q i)) hmarked
      _ = (1 - a) ^ t.card := by simp
  have hp := power_loss a ha ha1 t.card hra
  linarith

/--
Specialization to the multiplier loss `a = 1/m^2`.  The parameter `m` is real,
so this also applies to positive integer torus sizes after coercion.
-/
theorem square_scale_multiplier {ι : Type*} (s t : Finset ι) (q : ι → ℝ) (m : ℝ)
    (hts : t ⊆ s) (hm : 1 ≤ m)
    (hq : ∀ i ∈ s, |q i| ≤ 1)
    (hmarked : ∀ i ∈ t, |q i| ≤ 1 - 1 / m ^ 2)
    (hr : (t.card : ℝ) ≤ m ^ 2) :
    4 * (t.card : ℝ) ≤ 4 * m ^ 2 * (2 * (1 - ∏ i ∈ s, q i)) := by
  have hmpos : 0 < m := by linarith
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hmpos
  have hm2one : 1 ≤ m ^ 2 := by nlinarith
  have ha0 : 0 ≤ 1 / m ^ 2 := by positivity
  have ha1 : 1 / m ^ 2 ≤ 1 := (div_le_one hm2pos).mpr hm2one
  have hra : (t.card : ℝ) * (1 / m ^ 2) ≤ 1 := by
    rw [mul_one_div]
    exact (div_le_one hm2pos).mpr hr
  have h := finite_product_loss s t q (1 / m ^ 2) hts ha0 ha1 hq hmarked hra
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hm2pos)
  field_simp [ne_of_gt hmpos] at hmul
  nlinarith

end MeasureEquivalenceScalar
end MainProofScope22

/- Source module: TrigMultiplier -/
section MainProofScope23
/-!
# Trigonometric coordinate multiplier

This file checks the real-variable estimate used for each nonzero Fourier
coordinate.  In particular it applies to integer frequencies, without assuming
integrality.  It does not formalize the Fourier expansion or Parseval's identity.
-/

namespace MeasureEquivalenceTrig

/-- Jordan's inequality after scaling to a circle coordinate. -/
theorem scaled_jordan (m k : ℝ) (hm : 0 < m) (hk : 0 ≤ k)
    (hkm : k ≤ m / 2) :
    2 * k / m ≤ Real.sin (Real.pi * k / m) := by
  have hx0 : 0 ≤ Real.pi * k / m := by positivity
  have hx1 : Real.pi * k / m ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [Real.pi_pos]
  have h := Real.mul_le_sin hx0 hx1
  calc
    2 * k / m = 2 / Real.pi * (Real.pi * k / m) := by
      field_simp [Real.pi_ne_zero]
    _ ≤ Real.sin (Real.pi * k / m) := h

/-- The sine is bounded away from zero throughout the central frequency range. -/
theorem sine_frequency_lower (m k : ℝ) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hkm1 : k ≤ m - 1) :
    2 / m ≤ Real.sin (Real.pi * k / m) := by
  have hmpos : 0 < m := by linarith
  by_cases hkhalf : k ≤ m / 2
  · have hj := scaled_jordan m k hmpos (by linarith) hkhalf
    have hleft : 2 / m ≤ 2 * k / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    exact hleft.trans hj
  · have hk' : 1 ≤ m - k := by linarith
    have hkhalf' : m - k ≤ m / 2 := by linarith
    have hj := scaled_jordan m (m - k) hmpos (by linarith) hkhalf'
    have hleft : 2 / m ≤ 2 * (m - k) / m := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hmpos)
      linarith
    have hangle : Real.pi * (m - k) / m = Real.pi - Real.pi * k / m := by
      field_simp [ne_of_gt hmpos]
    rw [hangle, Real.sin_pi_sub] at hj
    exact hleft.trans hj

/--
The coordinate multiplier has a uniform absolute-value gap.  This is valid for
every real `m ≥ 2` and every real `k ∈ [1,m-1]`.
-/
theorem trig_coordinate_bound (m k : ℝ) (hm : 2 ≤ m)
    (hk1 : 1 ≤ k) (hkm1 : k ≤ m - 1) :
    |(1 + 2 * Real.cos (2 * Real.pi * k / m)) / 3| ≤ 1 - 1 / m ^ 2 := by
  have hmpos : 0 < m := by linarith
  have hm2pos : 0 < m ^ 2 := sq_pos_of_pos hmpos
  have hs := sine_frequency_lower m k hm hk1 hkm1
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 2 / m) hs 2
  have hsquare' : 4 * (1 / m ^ 2) ≤ Real.sin (Real.pi * k / m) ^ 2 := by
    convert hsquare using 1
    ring
  have hangle : 2 * Real.pi * k / m = 2 * (Real.pi * k / m) := by ring
  have hcos : Real.cos (2 * Real.pi * k / m) =
      1 - 2 * Real.sin (Real.pi * k / m) ^ 2 := by
    rw [hangle, Real.cos_two_mul_eq_one_sub]
  have hsmall : 1 / m ^ 2 ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ hm2pos (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith
  have hnonneg : 0 ≤ 1 / m ^ 2 := by positivity
  have hcoslower := Real.neg_one_le_cos (2 * Real.pi * k / m)
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

end MeasureEquivalenceTrig
end MainProofScope23

/- Source module: FiniteTorus -/
section MainProofScope24
/-!
Finite product tori: arbitrary single-coordinate shifts compared with the
uniform three-point product walk. This is stronger than the half-turn case.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]

def axisHom (j : ι) : ZMod m →+ (ι → ZMod m) where
  toFun u i := if i = j then u else 0
  map_zero' := by ext i; simp
  map_add' a b := by ext i; by_cases h : i = j <;> simp [h]

noncomputable def coordinateChar (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    AddChar (ZMod m) ℂ := χ.compAddMonoidHom (axisHom j)

lemma char_map_sum {A : Type*} [AddCommGroup A] (χ : AddChar A ℂ)
    {J : Type*} (s : Finset J) (f : J → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, χ.map_add_eq_mul, ih]

omit [NeZero m] in
lemma char_factor (χ : AddChar (ι → ZMod m) ℂ) (x : ι → ZMod m) :
    χ x = ∏ j, coordinateChar χ j (x j) := by
  have hx : x = ∑ j, axisHom j (x j) := by
    ext i
    simp [axisHom]
  conv_lhs => rw [hx, char_map_sum]
  rfl

def step (t : Fin 3) : ZMod m := ![-1, 0, 1] t

def shortShift (ε : ι → Fin 3) : ι → ZMod m := fun j => step (ε j)

noncomputable def q (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : ℝ :=
  (1 + 2 * (coordinateChar χ j 1).re) / 3

omit [Fintype ι] in
lemma coordinate_step_sum (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    (∑ t : Fin 3, coordinateChar χ j (step t)) = (3 : ℂ) * q χ j := by
  simp only [Fin.sum_univ_three, step, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, AddChar.map_zero_eq_one, AddChar.map_neg_eq_conj]
  apply Complex.ext <;> simp [q]
  ring

lemma random_character_sum (χ : AddChar (ι → ZMod m) ℂ) :
    (∑ ε : ι → Fin 3, χ (shortShift ε)) =
      (3 : ℂ) ^ Fintype.card ι * (∏ j, q χ j : ℝ) := by
  simp_rw [char_factor]
  change (∑ ε : ι → Fin 3, ∏ j, coordinateChar χ j (step (ε j))) = _
  rw [← Fintype.prod_sum (fun (j : ι) (t : Fin 3) => coordinateChar χ j (step t))]
  simp_rw [coordinate_step_sum]
  simp [Finset.prod_mul_distrib]

lemma random_energy_multiplier (χ : AddChar (ι → ZMod m) ℂ) :
    (∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2) =
      (3 : ℝ) ^ Fintype.card ι * (2 * (1 - ∏ j, q χ j)) := by
  have hre : (∑ ε : ι → Fin 3, (χ (shortShift ε)).re) =
      (3 : ℝ) ^ Fintype.card ι * ∏ j, q χ j := by
    have h := congrArg Complex.re (random_character_sum χ)
    have hreal : (3 : ℂ) ^ Fintype.card ι * (∏ j, q χ j : ℝ) =
        (((3 : ℝ) ^ Fintype.card ι * ∏ j, q χ j : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal] at h
    simpa only [Complex.re_sum, Complex.ofReal_re] using h
  simp_rw [Complex.norm_sub_one_sq_eq_of_norm_eq_one (χ.norm_apply _)]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [hre]
  ring

noncomputable def frequency (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : ZMod m :=
  AddChar.zmodAddEquiv.symm (coordinateChar χ j)

omit [Fintype ι] in
lemma coordinateChar_frequency (χ : AddChar (ι → ZMod m) ℂ) (j : ι) :
    coordinateChar χ j = AddChar.zmodAddEquiv (frequency χ j) := by
  simp [frequency]

lemma zmod_frequency_one (k : ZMod m) :
    ((AddChar.zmodAddEquiv k) 1).re =
      Real.cos (2 * Real.pi * (k.val : ℝ) / (m : ℝ)) := by
  change ((AddChar.zmod m k 1 : Circle) : ℂ).re = _
  have h := AddChar.zmod_intCast m (k.val : ℤ) (1 : ℤ)
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_one,
    mul_one] at h
  rw [h, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

omit [Fintype ι] in
lemma q_abs_le_one (χ : AddChar (ι → ZMod m) ℂ) (j : ι) : |q χ j| ≤ 1 := by
  have h := Complex.abs_re_le_norm (coordinateChar χ j 1)
  rw [(coordinateChar χ j).norm_apply] at h
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  unfold q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

omit [Fintype ι] in
lemma q_abs_gap (χ : AddChar (ι → ZMod m) ℂ) (hm : 2 ≤ m) (j : ι)
    (hj : frequency χ j ≠ 0) : |q χ j| ≤ 1 - 1 / (m : ℝ) ^ 2 := by
  have hk1 : 1 ≤ ((frequency χ j).val : ℝ) := by
    exact_mod_cast (ZMod.val_pos.mpr hj)
  have hkm : ((frequency χ j).val : ℝ) ≤ (m : ℝ) - 1 := by
    have h := (frequency χ j).val_lt
    have h' : (frequency χ j).val + 1 ≤ m := h
    have hreal : ((frequency χ j).val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h'
    linarith
  have h := MeasureEquivalenceTrig.trig_coordinate_bound (m : ℝ)
    (frequency χ j).val (by exact_mod_cast hm) hk1 hkm
  simpa only [q, coordinateChar_frequency, zmod_frequency_one] using h

noncomputable def active (χ : AddChar (ι → ZMod m) ℂ) : Finset ι :=
  Finset.univ.filter fun j => frequency χ j ≠ 0

lemma long_multiplier_le (χ : AddChar (ι → ZMod m) ℂ) (a : ι → ZMod m) :
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤ 4 * ((active χ).card : ℝ) := by
  have hpoint (j : ι) : ‖χ (axisHom j (a j)) - 1‖ ^ 2 ≤
      if frequency χ j ≠ 0 then (4 : ℝ) else 0 := by
    by_cases hj : frequency χ j ≠ 0
    · rw [if_pos hj]
      have hnorm := norm_sub_le (χ (axisHom j (a j))) (1 : ℂ)
      simp only [χ.norm_apply, norm_one] at hnorm
      have hn := norm_nonneg (χ (axisHom j (a j)) - 1)
      nlinarith
    · rw [if_neg hj]
      have hz : frequency χ j = 0 := not_ne_iff.mp hj
      change ‖coordinateChar χ j (a j) - 1‖ ^ 2 ≤ 0
      rw [coordinateChar_frequency, hz]
      have hzmap : AddChar.zmodAddEquiv (0 : ZMod m) =
          (0 : AddChar (ZMod m) ℂ) :=
        map_zero (AddChar.zmodAddEquiv : ZMod m ≃+ AddChar (ZMod m) ℂ)
      rw [hzmap]
      simp
  calc
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
        ∑ j, if frequency χ j ≠ 0 then (4 : ℝ) else 0 :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = 4 * ((active χ).card : ℝ) := by
      rw [← Finset.sum_filter]
      simp [active, mul_comm]

theorem torus_multiplier (χ : AddChar (ι → ZMod m) ℂ) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2 := by
  have hsub : active χ ⊆ Finset.univ := Finset.filter_subset _ _
  have hcard : (active χ).card ≤ m ^ 2 :=
    (Finset.card_le_card hsub).trans (by simpa using hn)
  have hscalar := MeasureEquivalenceScalar.square_scale_multiplier
    Finset.univ (active χ) (q χ) (m : ℝ) hsub
    (by exact_mod_cast (show 1 ≤ m by omega))
    (fun j _ => q_abs_le_one χ j)
    (fun j hj => q_abs_gap χ hm j (Finset.mem_filter.mp hj).2)
    (by exact_mod_cast hcard)
  calc
    (∑ j, ‖χ (axisHom j (a j)) - 1‖ ^ 2) ≤
        4 * ((active χ).card : ℝ) := long_multiplier_le χ a
    _ ≤ 4 * (m : ℝ) ^ 2 * (2 * (1 - ∏ j, q χ j)) := hscalar
    _ = (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ‖χ (shortShift ε) - 1‖ ^ 2 := by
      rw [random_energy_multiplier]
      field_simp

/-- The finite-torus Hilbert inequality, with arbitrary shifts on each axis.
The missing common average over `x` cancels on both sides. -/
theorem finite_torus_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ∑ x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ∑ x, ‖F (x + shortShift ε) - F x‖ ^ 2 :=
  MeasureEquivalenceFourier.spectral_comparison
    (fun j => axisHom j (a j)) shortShift _ (fun χ => torus_multiplier χ a hm hn) F

/-- The same inequality for arbitrary real inner product spaces. The finite
range spans a finite-dimensional subspace, whose orthonormal coordinates embed
isometrically into a complex Euclidean space. -/
theorem finite_torus_real_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, ∑ x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      (4 * (m : ℝ) ^ 2 / (3 : ℝ) ^ Fintype.card ι) *
        ∑ ε : ι → Fin 3, ∑ x, ‖F (x + shortShift ε) - F x‖ ^ 2 := by
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range F)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range F)
  let f : (ι → ZMod m) → S := fun x =>
    ⟨F x, Submodule.subset_span (Set.mem_range_self x)⟩
  let b := stdOrthonormalBasis ℝ S
  let g : (ι → ZMod m) → EuclideanSpace ℂ (Fin (Module.finrank ℝ S)) :=
    fun x => WithLp.toLp 2 (fun i => ((b.repr (f x) i : ℝ) : ℂ))
  have hnorm (x y : ι → ZMod m) : ‖g x - g y‖ ^ 2 = ‖F x - F y‖ ^ 2 := by
    calc
      ‖g x - g y‖ ^ 2 = ‖b.repr (f x) - b.repr (f y)‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
        apply Finset.sum_congr rfl
        intro i _
        simp [g, PiLp.sub_apply, ← Complex.ofReal_sub]
      _ = ‖f x - f y‖ ^ 2 := by rw [← map_sub, b.repr.norm_map]
      _ = ‖F x - F y‖ ^ 2 := rfl
  have h := finite_torus_hilbert g a hm hn
  simpa only [hnorm] using h

/-- Uniform-expectation form of the strengthened inequality. -/
theorem finite_torus_hilbert_expect {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (finite_torus_hilbert F a hm hn)
    (Nat.cast_nonneg (Fintype.card (ι → ZMod m)) : (0 : ℝ) ≤ _)
  convert h using 1
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- Uniform-expectation form for real targets. -/
theorem finite_torus_real_hilbert_expect {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E) (a : ι → ZMod m)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j (a j)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) := by
  simp_rw [Fintype.expect_eq_sum_div_card]
  rw [← Finset.sum_div, ← Finset.sum_div]
  have h := div_le_div_of_nonneg_right (finite_torus_real_hilbert F a hm hn)
    (Nat.cast_nonneg (Fintype.card (ι → ZMod m)) : (0 : ℝ) ≤ _)
  convert h using 1
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The original real-Hilbert half-turn inequality is an immediate instance.
No parity assumption is needed for the inequality; for even `m` this is the
half-turn of order two. -/
theorem half_turn_real_hilbert {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (F : (ι → ZMod m) → E)
    (hm : 2 ≤ m) (hn : Fintype.card ι ≤ m ^ 2) :
    (∑ j, 𝔼 x, ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖ ^ 2) ≤
      4 * (m : ℝ) ^ 2 *
        (𝔼 ε : ι → Fin 3, 𝔼 x, ‖F (x + shortShift ε) - F x‖ ^ 2) :=
  finite_torus_real_hilbert_expect F (fun _ => ((m / 2 : ℕ) : ZMod m)) hm hn

end MeasureEquivalenceTorus
end MainProofScope24

/- Source module: GridObstruction -/
section MainProofScope25
/-! The dimension-uniform contradiction, including the two continuity
quantifiers. Actual circle-sequence grids are instantiated in a separate file. -/

open Filter Topology
open scoped Topology BigOperators

namespace MeasureEquivalenceGrid

open MeasureEquivalenceTorus

variable {H E : Type*} [NormedAddCommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inverse continuity at the identity provides one bound for all long steps. -/
lemma inducing_long_bound (Ψ : H → E) (hΨ : IsInducing Ψ) :
    ∃ c > 0, ∀ h : H, (1 / 4 : ℝ) ≤ ‖h‖ → c ≤ ‖Ψ h - Ψ 0‖ := by
  have hball : Metric.ball (0 : H) (1 / 4) ∈ 𝓝 (0 : H) :=
    Metric.ball_mem_nhds _ (by norm_num)
  rw [hΨ.nhds_eq_comap 0, Filter.mem_comap] at hball
  obtain ⟨s, hs, hsub⟩ := hball
  obtain ⟨c, hc, hcs⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨c, hc, fun h hh => ?_⟩
  by_contra! hcontra
  have hm : h ∈ Metric.ball (0 : H) (1 / 4) :=
    hsub (hcs (by simpa [Metric.mem_ball, dist_eq_norm] using hcontra))
  have : ‖h‖ < (1 / 4 : ℝ) := by simpa [Metric.mem_ball, dist_eq_norm] using hm
  linarith

/-- One finite torus is already contradictory when the long steps all have
length at least c and all the short steps have length at most c/3. -/
theorem finite_grid_gap {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    (F : (Fin (m ^ 2) → ZMod m) → E) (c : ℝ) (hc : 0 < c)
    (hlong : ∀ j x, c ≤
      ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖)
    (hshort : ∀ ε x,
      ‖F (x + shortShift ε) - F x‖ ≤ c / 3) : False := by
  classical
  have hlow : (m : ℝ) ^ 2 * c ^ 2 ≤
      ∑ j : Fin (m ^ 2), 𝔼 x,
        ‖F (x + axisHom j ((m / 2 : ℕ) : ZMod m)) - F x‖ ^ 2 := by
    calc
      (m : ℝ) ^ 2 * c ^ 2 = ∑ _j : Fin (m ^ 2), 𝔼 _x : Fin (m ^ 2) → ZMod m,
          c ^ 2 := by simp
      _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.expect_le_expect fun x _ => by
        exact pow_le_pow_left₀ hc.le (hlong j x) 2
  have hupp : (𝔼 ε : Fin (m ^ 2) → Fin 3, 𝔼 x,
      ‖F (x + shortShift ε) - F x‖ ^ 2) ≤ (c / 3) ^ 2 := by
    calc
      _ ≤ (𝔼 _ε : Fin (m ^ 2) → Fin 3, 𝔼 _x : Fin (m ^ 2) → ZMod m,
          (c / 3) ^ 2) :=
        Finset.expect_le_expect fun ε _ => Finset.expect_le_expect fun x _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hshort ε x) 2
      _ = _ := by simp
  have htor := half_turn_real_hilbert F hm (by simp)
  have hbound : (m : ℝ) ^ 2 * c ^ 2 ≤ 4 * (m : ℝ) ^ 2 * (c / 3) ^ 2 :=
    hlow.trans (htor.trans (mul_le_mul_of_nonneg_left hupp (by positivity)))
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hpos : 0 < (m : ℝ) ^ 2 * c ^ 2 := by positivity
  nlinarith

/-- An abstract grid criterion with the complete order of quantifiers.
The grid, modulus and dimension may depend on delta; the continuity constants
and long-step lower bound cannot depend on them. -/
theorem no_invariant_hilbert_embedding
    (hgrids : ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
      (grid : (Fin (m ^ 2) → ZMod m) →+ H),
      (∀ j, (1 / 4 : ℝ) ≤ ‖grid (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖grid (shortShift ε)‖ < δ))
    (Ψ : H → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False := by
  obtain ⟨c, hc, hlong⟩ := inducing_long_bound Ψ hΨ.isInducing
  obtain ⟨δ, hδ, hsmall⟩ :=
    Metric.continuousAt_iff.mp (hΨ.continuous.continuousAt (x := 0)) (c / 3)
      (by positivity)
  obtain ⟨m, hm, grid, hgridlong, hgridshort⟩ := hgrids δ hδ
  letI : NeZero m := ⟨by omega⟩
  have hdisp (x y : Fin (m ^ 2) → ZMod m) :
      ‖Ψ (grid (x + y)) - Ψ (grid x)‖ = ‖Ψ (grid y) - Ψ 0‖ := by
    rw [map_add, add_comm (grid x) (grid y)]
    simpa only [zero_add] using hinv (grid y) 0 (grid x)
  apply finite_grid_gap hm (Ψ ∘ grid) c hc
  · intro j x
    simpa only [Function.comp_apply, hdisp] using hlong _ (hgridlong j)
  · intro ε x
    rw [Function.comp_apply, Function.comp_apply, hdisp]
    apply le_of_lt
    simpa only [dist_eq_norm] using hsmall
      (show dist (grid (shortShift ε)) 0 < δ by simpa using hgridshort ε)

end MeasureEquivalenceGrid
end MainProofScope25

/- Source module: CircleGrids -/
section MainProofScope26
open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircle

open MeasureEquivalenceTorus MeasureEquivalenceGrid

abbrev Hp (p : ℝ≥0∞) := lp (fun _ : ℕ => UnitAddCircle) p

variable (p : ℝ≥0∞) {m n : ℕ} [NeZero m]

def gridValue (x : Fin n → ZMod m) (k : ℕ) : UnitAddCircle :=
  if hk : k < n then ZMod.toAddCircle (x ⟨k, hk⟩) else 0

def grid : (Fin n → ZMod m) →+ Hp p where
  toFun x := ⟨gridValue x, (memℓp_zero (by
    apply (Finset.finite_toSet (Finset.range n)).subset
    intro k hk
    by_contra hkn
    have : ¬ k < n := by simpa using hkn
    exact hk (by simp [gridValue, this]))).of_exponent_ge (by positivity)⟩
  map_zero' := by
    apply lp.ext
    funext k
    change gridValue (0 : Fin n → ZMod m) k = (0 : UnitAddCircle)
    simp [gridValue]
  map_add' x y := by
    ext k
    change gridValue (x + y) k = gridValue x k + gridValue y k
    simp only [gridValue]
    split_ifs <;> simp

@[simp] lemma grid_apply (x : Fin n → ZMod m) (k : ℕ) :
    grid p x k = gridValue x k := rfl

lemma grid_apply_fin (x : Fin n → ZMod m) (j : Fin n) :
    grid p x j = ZMod.toAddCircle (x j) := by simp [gridValue]

lemma grid_apply_ge (x : Fin n → ZMod m) {k : ℕ} (hk : n ≤ k) :
    grid p x k = 0 := by simp [gridValue, not_lt.mpr hk]

lemma circle_step_bound (t : Fin 3) :
    ‖ZMod.toAddCircle (step (m := m) t)‖ ≤ 1 / (m : ℝ) := by
  have hbase : ‖((1 / (m : ℝ) : ℝ) : UnitAddCircle)‖ ≤ 1 / (m : ℝ) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
      using (QuotientAddGroup.norm_mk_le_norm
        (m := (1 / (m : ℝ) : ℝ)) (S := AddSubgroup.zmultiples (1 : ℝ)))
  have hone : ZMod.toAddCircle (1 : ZMod m) = ((1 / (m : ℝ) : ℝ) : UnitAddCircle) := by
    simpa using ZMod.toAddCircle_natCast (N := m) 1
  fin_cases t <;> simp [step, map_neg, hone] <;> simpa [one_div] using hbase

lemma half_turn_value (heven : Even m) :
    ZMod.toAddCircle ((m / 2 : ℕ) : ZMod m) = ((1 / 2 : ℝ) : UnitAddCircle) := by
  rw [ZMod.toAddCircle_natCast]
  congr 1
  have hmul : m / 2 * 2 = m := Nat.div_mul_cancel heven.two_dvd
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hreal : (m / 2 : ℕ) * (2 : ℝ) = m := by exact_mod_cast hmul
  apply (div_eq_iff hm).mpr
  linarith

lemma grid_long_bound (hp : p ≠ 0) (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖grid p (axisHom j ((m / 2 : ℕ) : ZMod m))‖ := by
  have h := lp.norm_apply_le_norm hp (grid p (axisHom j ((m / 2 : ℕ) : ZMod m))) j
  rw [grid_apply_fin] at h
  simp only [axisHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, ite_true] at h
  rw [half_turn_value heven] at h
  have hnorm : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = (1 / 2 : ℝ) := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  rw [hnorm] at h
  exact (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num).trans h

lemma grid_short_coordinate (ε : Fin n → Fin 3) (k : ℕ) :
    ‖grid (m := m) p (shortShift ε) k‖ ≤ 1 / (m : ℝ) := by
  by_cases hk : k < n
  · simpa [gridValue, hk, shortShift] using circle_step_bound (m := m) (ε ⟨k, hk⟩)
  · simp [gridValue, hk]

lemma grid_short_sup (ε : Fin n → Fin 3) :
    ‖grid (m := m) ⊤ (shortShift ε)‖ ≤ 1 / (m : ℝ) :=
  lp.norm_le_of_forall_le (by positivity) (grid_short_coordinate ⊤ ε)

lemma grid_norm_rpow (hp : 0 < p.toReal) (x : Fin n → ZMod m) :
    ‖grid p x‖ ^ p.toReal = ∑ k ∈ Finset.range n, ‖grid p x k‖ ^ p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp]
  apply tsum_eq_sum
  intro k hk
  rw [grid_apply_ge p x (by simpa using hk), norm_zero, Real.zero_rpow hp.ne']

lemma grid_short_rpow (hp : 0 < p.toReal) (ε : Fin n → Fin 3) :
    ‖grid (m := m) p (shortShift ε)‖ ^ p.toReal ≤
      (n : ℝ) * (1 / (m : ℝ)) ^ p.toReal := by
  rw [grid_norm_rpow p hp]
  calc
    _ ≤ ∑ _k ∈ Finset.range n, (1 / (m : ℝ)) ^ p.toReal :=
      Finset.sum_le_sum fun k _ => Real.rpow_le_rpow (norm_nonneg _)
        (grid_short_coordinate p ε k) hp.le
    _ = _ := by simp

lemma grid_square_short_rpow (hp : 0 < p.toReal) (ε : Fin (m ^ 2) → Fin 3) :
    ‖grid (m := m) p (shortShift ε)‖ ^ p.toReal ≤ (m : ℝ) ^ (2 - p.toReal) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (NeZero.pos m)
  convert grid_short_rpow p hp ε using 1
  rw [Real.rpow_sub hm, Real.rpow_two]
  simp [Nat.cast_pow, one_div, Real.inv_rpow, div_eq_mul_inv]

/-- Even moduli can be chosen arbitrarily far out; the dimension is then m². -/
lemma exists_even_rpow_small {r δ : ℝ} (hr : r < 0) (hδ : 0 < δ) :
    ∃ m : ℕ, 2 ≤ m ∧ Even m ∧ (m : ℝ) ^ r < δ := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : ∀ᶠ m : ℕ in atTop, (m : ℝ) ^ r < δ := ht.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  refine ⟨2 * (N + 1), by omega, ⟨N + 1, by omega⟩, hN _ (by omega)⟩

/-- The circle null-sequence group, with the inherited supremum norm. -/
def H0subgroup : AddSubgroup (Hp ⊤) where
  carrier := {x | Tendsto (fun k => x k) atTop (𝓝 0)}
  zero_mem' := by simpa using tendsto_const_nhds
  add_mem' hx hy := by simpa using hx.add hy
  neg_mem' hx := by simpa using hx.neg

abbrev H0 := H0subgroup

lemma grid_null (x : Fin n → ZMod m) : grid ⊤ x ∈ H0subgroup := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with k hk
  exact (grid_apply_ge ⊤ x hk).symm

def grid0 : (Fin n → ZMod m) →+ H0 :=
  (grid ⊤).codRestrict H0subgroup grid_null

lemma grid0_long_bound (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖grid0 (axisHom j ((m / 2 : ℕ) : ZMod m))‖ :=
  grid_long_bound ⊤ (by simp) heven j

lemma grid0_short_bound (ε : Fin n → Fin 3) :
    ‖grid0 (m := m) (shortShift ε)‖ ≤ 1 / (m : ℝ) := grid_short_sup ε

theorem H0_has_small_grids : ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
    (g : (Fin (m ^ 2) → ZMod m) →+ H0),
    (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
    (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro δ hδ
  obtain ⟨m, hm, heven, hsmall⟩ := exists_even_rpow_small (r := -1) (by norm_num) hδ
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, grid0, grid0_long_bound heven, fun ε => ?_⟩
  apply (grid0_short_bound ε).trans_lt
  simpa [Real.rpow_neg_one, one_div] using hsmall

theorem Hp_has_small_grids [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ∀ δ > 0, ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ Hp p),
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro δ hδ
  have hp0 : 0 < p.toReal := by linarith
  have hpn : p ≠ 0 := by intro hz; norm_num [hz] at hp
  obtain ⟨m, hm, heven, hsmall⟩ := exists_even_rpow_small
    (r := 2 - p.toReal) (by linarith) (Real.rpow_pos_of_pos hδ p.toReal)
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, grid p, grid_long_bound p hpn heven, fun ε => ?_⟩
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hδ.le hp0).mp
    ((grid_square_short_rpow p hp0 ε).trans_lt hsmall)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Concrete null-circle-sequence obstruction, with no grid assumptions. -/
theorem no_H0_invariant_hilbert_embedding (Ψ : H0 → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False :=
  no_invariant_hilbert_embedding H0_has_small_grids Ψ hΨ hinv

/-- Concrete finite-p circle-sequence obstruction. `2 < p.toReal` excludes
the infinite exponent, and `[Fact (1 ≤ p)]` supplies its standard lp metric. -/
theorem no_Hp_invariant_hilbert_embedding [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (Ψ : Hp p → E) (hΨ : IsEmbedding Ψ)
    (hinv : ∀ h k t, ‖Ψ (h + t) - Ψ (k + t)‖ = ‖Ψ h - Ψ k‖) : False :=
  no_invariant_hilbert_embedding (Hp_has_small_grids p hp) Ψ hΨ hinv

end MeasureEquivalenceCircle
end
end MainProofScope26

/- Source module: CircleTopology -/
section MainProofScope27
open Filter Topology Set TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleTopology

open MeasureEquivalenceCircle

abbrev K := ℕ → UnitAddCircle

variable (p : ℝ≥0∞) [Fact (1 ≤ p)]

def trunc (s : Finset ℕ) (x : K) : Hp p :=
  ∑ i ∈ s, lp.single p i (x i)

lemma continuous_trunc (s : Finset ℕ) : Continuous (trunc p s) := by
  apply continuous_finsetSum
  intro i hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => UnitAddCircle) p i).continuous.comp
    (continuous_apply i)

lemma dense_trunc (hp : p ≠ ⊤) : Dense (⋃ s : Finset ℕ, range (trunc p s)) := by
  intro x
  have hx := lp.hasSum_single hp x
  apply mem_closure_of_tendsto hx
  exact Filter.Eventually.of_forall (fun s => mem_iUnion.mpr ⟨s, ⟨(x : K), rfl⟩⟩)

theorem hp_separable (hp : p ≠ ⊤) : SeparableSpace (Hp p) := by
  apply (dense_trunc p hp).isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (continuous_trunc p s))

lemma continuous_hp_coordinates : Continuous (fun h : Hp p => (h : K)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval p i).continuous

theorem hp_polish (hp : p ≠ ⊤) : PolishSpace (Hp p) := by
  let := hp_separable p hp
  infer_instance

lemma h0_closed : IsClosed (H0subgroup : Set (Hp ⊤)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u x hu hx
  change Tendsto (fun k => x k) atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := (Metric.tendsto_nhds.mp hx (ε / 2) (by positivity)).exists
  have huj : Tendsto (fun k => u j k) atTop (𝓝 0) := hu j
  filter_upwards [Metric.tendsto_nhds.mp huj (ε / 2) (by positivity)] with k hk
  have hcoord : dist (x k) (u j k) ≤ dist x (u j) := by
    simpa only [dist_eq_norm, lp.coeFn_sub, Pi.sub_apply] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (x - u j) k
  calc
    dist (x k) 0 ≤ dist (x k) (u j k) + dist (u j k) 0 := dist_triangle _ _ _
    _ ≤ dist x (u j) + dist (u j k) 0 := add_le_add hcoord le_rfl
    _ < ε := by rw [dist_comm x]; linarith

theorem h0_complete : CompleteSpace H0 := h0_closed.isComplete.completeSpace_coe

omit [Fact (1 ≤ p)] in
lemma trunc_apply (s : Finset ℕ) (x : K) (k : ℕ) :
    trunc p s x k = if k ∈ s then x k else 0 := by
  simp only [trunc, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

lemma trunc_null (s : Finset ℕ) (x : K) : trunc ⊤ s x ∈ H0subgroup := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (s.sup id)] with k hk
  have hkn : k ∉ s := by
    intro hmem
    have : k ≤ s.sup id := Finset.le_sup (f := id) hmem
    omega
  simp [trunc_apply, hkn]

def trunc0 (s : Finset ℕ) (x : K) : H0 := ⟨trunc ⊤ s x, trunc_null s x⟩

lemma continuous_trunc0 (s : Finset ℕ) : Continuous (trunc0 s) :=
  (continuous_trunc ⊤ s).subtype_mk _

lemma tendsto_trunc0 (x : H0) :
    Tendsto (fun N : ℕ => trunc0 (Finset.range N) ((x : Hp ⊤) : K)) atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hx : Tendsto (fun k => (x : Hp ⊤) k) atTop (𝓝 0) := x.property
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendsto_nhds.mp hx (ε / 2) (by positivity))
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (b := ε / 2) _ (by linarith)
  change ‖trunc ⊤ (Finset.range n) ((x : Hp ⊤) : K) - (x : Hp ⊤)‖ ≤ ε / 2
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  simp only [lp.coeFn_sub, Pi.sub_apply, trunc_apply, Finset.mem_range]
  split_ifs with hk
  · simp; positivity
  · have hNk : N ≤ k := by omega
    simpa only [zero_sub, norm_neg, dist_zero_right] using (hN k hNk).le

lemma dense_trunc0 : Dense (⋃ s : Finset ℕ, range (trunc0 s)) := by
  intro x
  apply mem_closure_of_tendsto (tendsto_trunc0 x)
  exact Filter.Eventually.of_forall (fun N =>
    mem_iUnion.mpr ⟨Finset.range N, ⟨((x : Hp ⊤) : K), rfl⟩⟩)

theorem h0_separable : SeparableSpace H0 := by
  apply dense_trunc0.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (continuous_trunc0 s))

theorem h0_polish : PolishSpace H0 := by
  let := h0_complete
  let := h0_separable
  infer_instance

lemma continuous_h0_coordinates : Continuous (fun h : H0 => ((h : Hp ⊤) : K)) :=
  (continuous_hp_coordinates ⊤).comp continuous_subtype_val

end MeasureEquivalenceCircleTopology
end
end MainProofScope27

/- Source module: CircleReduction -/
section MainProofScope28
open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleReduction

/-!
The domain and codomain sequence spaces below have their product topologies.
The lp relations are actual summability predicates, and the null relations
are actual convergence-to-zero predicates. All chord estimates and the
even/odd real interleaving are proved, rather than supplied as hypotheses.
-/

def circleEmbed (t : UnitAddCircle) : ℂ := AddCircle.toCircle t

lemma continuous_circleEmbed : Continuous circleEmbed :=
  continuous_subtype_val.comp AddCircle.continuous_toCircle

@[simp] lemma circleEmbed_re_mk (r : ℝ) :
    (circleEmbed (r : UnitAddCircle)).re = Real.cos (2 * Real.pi * r) := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_re]

@[simp] lemma circleEmbed_im_mk (r : ℝ) :
    (circleEmbed (r : UnitAddCircle)).im = Real.sin (2 * Real.pi * r) := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im]

lemma circle_rep (t : UnitAddCircle) :
    ∃ r : ℝ, (r : UnitAddCircle) = t ∧ |r| ≤ 1 / 2 ∧ ‖t‖ = |r| := by
  obtain ⟨x⟩ := t
  have hz : (((round x : ℤ) : ℝ) : UnitAddCircle) = 0 := by
    apply (AddCircle.coe_eq_zero_iff _).2
    exact ⟨round x, by simp⟩
  refine ⟨x - round x, ?_, abs_sub_round x, UnitAddCircle.norm_eq⟩
  simp [hz]
  rfl

lemma chord_real (r : ℝ) :
    ‖circleEmbed (r : UnitAddCircle) - 1‖ = 2 * |Real.sin (Real.pi * r)| := by
  simp only [circleEmbed, AddCircle.toCircle_apply_mk, div_one, Circle.coe_exp]
  rw [mul_comm _ Complex.I, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hr : 2 * Real.pi * r / 2 = Real.pi * r := by ring
  rw [hr, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma chord_bounds (t : UnitAddCircle) :
    4 * ‖t‖ ≤ ‖circleEmbed t - 1‖ ∧
    ‖circleEmbed t - 1‖ ≤ (2 * Real.pi) * ‖t‖ := by
  obtain ⟨r, rfl, hr, hn⟩ := circle_rep t
  rw [chord_real, hn]
  have habs : |Real.pi * r| = Real.pi * |r| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hb : |Real.pi * r| ≤ Real.pi / 2 := by
    rw [habs]; nlinarith [Real.pi_pos]
  have hlo := Real.mul_abs_le_abs_sin hb
  have hhi := Real.abs_sin_le_abs (x := Real.pi * r)
  rw [habs] at hlo hhi
  have hcalc : 2 / Real.pi * (Real.pi * |r|) = 2 * |r| := by
    field_simp
  rw [hcalc] at hlo
  constructor <;> nlinarith

lemma circleEmbed_add (s t : UnitAddCircle) :
    circleEmbed (s + t) = circleEmbed s * circleEmbed t := by
  exact congrArg (fun c : Circle => (c : ℂ)) (AddCircle.toCircle_add s t)

@[simp] lemma circleEmbed_norm (t : UnitAddCircle) : ‖circleEmbed t‖ = 1 :=
  (AddCircle.toCircle t).norm_coe

lemma chord_sub (s t : UnitAddCircle) :
    ‖circleEmbed s - circleEmbed t‖ = ‖circleEmbed (s - t) - 1‖ := by
  have hmul : circleEmbed (s - t) * circleEmbed t = circleEmbed s := by
    rw [← circleEmbed_add, sub_add_cancel]
  have heq : circleEmbed s - circleEmbed t =
      (circleEmbed (s - t) - 1) * circleEmbed t := by
    rw [sub_mul, one_mul, hmul]
  rw [heq, norm_mul, circleEmbed_norm, mul_one]

lemma chord_sub_bounds (s t : UnitAddCircle) :
    4 * ‖s - t‖ ≤ ‖circleEmbed s - circleEmbed t‖ ∧
    ‖circleEmbed s - circleEmbed t‖ ≤ (2 * Real.pi) * ‖s - t‖ := by
  rw [chord_sub]
  exact chord_bounds (s - t)

lemma memlp_circle_iff_complex (p : ℝ≥0∞) (x y : ℕ → UnitAddCircle) :
    Memℓp (fun n => x n - y n) p ↔
    Memℓp (fun n => circleEmbed (x n) - circleEmbed (y n)) p := by
  constructor
  · intro h
    exact (h.norm.const_mul (2 * Real.pi)).mono fun n => (chord_sub_bounds _ _).2
  · intro h
    apply (h.norm.const_mul (1 / 4 : ℝ)).mono
    intro n
    have := (chord_sub_bounds (x n) (y n)).1
    linarith

lemma memlp_complex_iff_re_im (p : ℝ≥0∞) (z : ℕ → ℂ) :
    Memℓp z p ↔ Memℓp (fun n => (z n).re) p ∧ Memℓp (fun n => (z n).im) p := by
  constructor
  · intro h
    constructor
    · exact h.norm.mono fun n => Complex.abs_re_le_norm (z n)
    · exact h.norm.mono fun n => Complex.abs_im_le_norm (z n)
  · rintro ⟨hr, hi⟩
    exact (hr.norm.add hi.norm).mono fun n => Complex.norm_le_abs_re_add_abs_im (z n)

def pairCoords (a b : ℕ → ℝ) (i : ℕ × Fin 2) : ℝ :=
  if i.2 = 0 then a i.1 else b i.1

def interleave (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  pairCoords a b (Nat.divModEquiv 2 n)

@[simp] lemma interleave_even (a b : ℕ → ℝ) (n : ℕ) :
    interleave a b (2 * n) = a n := by
  simp [interleave, pairCoords, Nat.divModEquiv, Nat.mul_comm]

@[simp] lemma interleave_odd (a b : ℕ → ℝ) (n : ℕ) :
    interleave a b (2 * n + 1) = b n := by
  simp [interleave, pairCoords, Nat.divModEquiv, Nat.mul_comm]
  have hd : (n * 2 + 1) / 2 = n := by omega
  have hm : ¬ 2 ∣ n * 2 + 1 := by omega
  simp [hm, hd]

lemma interleave_sub (a b c d : ℕ → ℝ) :
    interleave a b - interleave c d = interleave (a - c) (b - d) := by
  ext n
  simp only [interleave, pairCoords, Pi.sub_apply]
  split_ifs <;> rfl

lemma memlp_interleave (p : ℝ≥0∞) (hp : 0 < p.toReal) (a b : ℕ → ℝ) :
    Memℓp (interleave a b) p ↔ Memℓp a p ∧ Memℓp b p := by
  simp only [memℓp_gen_iff hp]
  change Summable ((fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal) ∘
    Nat.divModEquiv 2) ↔ _
  rw [(Nat.divModEquiv 2).summable_iff]
  constructor
  · intro h
    constructor
    · simpa [Function.comp_def, pairCoords] using
        h.comp_injective (f := fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal)
          (i := fun n : ℕ => (n, (0 : Fin 2))) (by intro n m h; exact congrArg Prod.fst h)
    · simpa [Function.comp_def, pairCoords] using
        h.comp_injective (f := fun i : ℕ × Fin 2 => ‖pairCoords a b i‖ ^ p.toReal)
          (i := fun n : ℕ => (n, (1 : Fin 2))) (by intro n m h; exact congrArg Prod.fst h)
  · rintro ⟨ha, hb⟩
    apply (summable_prod_of_nonneg (by intro i; positivity)).2
    constructor
    · intro n
      exact (hasSum_fintype (fun j : Fin 2 => ‖pairCoords a b (n, j)‖ ^ p.toReal)).summable
    · simpa [tsum_fintype, Fin.sum_univ_two, pairCoords] using ha.add hb

def realEmbed (x : ℕ → UnitAddCircle) : ℕ → ℝ :=
  interleave (fun n => (circleEmbed (x n)).re) (fun n => (circleEmbed (x n)).im)

lemma continuous_realEmbed : Continuous realEmbed := by
  apply continuous_pi
  intro n
  dsimp [realEmbed, interleave, pairCoords]
  split_ifs
  · exact Complex.continuous_re.comp (continuous_circleEmbed.comp (continuous_apply _))
  · exact Complex.continuous_im.comp (continuous_circleEmbed.comp (continuous_apply _))

@[simp] lemma realEmbed_even (x : ℕ → UnitAddCircle) (n : ℕ) :
    realEmbed x (2 * n) = (circleEmbed (x n)).re := by simp [realEmbed]

@[simp] lemma realEmbed_odd (x : ℕ → UnitAddCircle) (n : ℕ) :
    realEmbed x (2 * n + 1) = (circleEmbed (x n)).im := by simp [realEmbed]

def CircleLpRel (p : ℝ≥0∞) (x y : ℕ → UnitAddCircle) : Prop :=
  Memℓp (fun n => x n - y n) p

def RealLpRel (p : ℝ≥0∞) (x y : ℕ → ℝ) : Prop :=
  Memℓp (fun n => x n - y n) p

theorem circle_real_lp_reduction (p : ℝ≥0∞) (hp : 0 < p.toReal)
    (x y : ℕ → UnitAddCircle) :
    CircleLpRel p x y ↔ RealLpRel p (realEmbed x) (realEmbed y) := by
  rw [CircleLpRel, memlp_circle_iff_complex, memlp_complex_iff_re_im]
  change _ ↔ Memℓp (realEmbed x - realEmbed y) p
  rw [realEmbed, realEmbed, interleave_sub, memlp_interleave p hp]
  rfl

lemma null_circle_iff_complex (x y : ℕ → UnitAddCircle) :
    Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
    Tendsto (fun n => circleEmbed (x n) - circleEmbed (y n)) atTop (𝓝 0) := by
  conv_lhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  constructor
  · intro h
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (chord_sub_bounds (x n) (y n)).2)
    simpa using h.const_mul (2 * Real.pi)
  · intro h
    apply squeeze_zero (fun n => norm_nonneg _)
      (g := fun n => (1 / 4 : ℝ) * ‖circleEmbed (x n) - circleEmbed (y n)‖)
    · intro n
      have := (chord_sub_bounds (x n) (y n)).1
      linarith
    · simpa using h.const_mul (1 / 4 : ℝ)

lemma null_interleave (a b : ℕ → ℝ) :
    Tendsto (interleave a b) atTop (𝓝 0) ↔
    Tendsto a atTop (𝓝 0) ∧ Tendsto b atTop (𝓝 0) := by
  simp only [Metric.tendsto_atTop]
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n) (by omega)
    · intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      refine ⟨N, fun n hn => ?_⟩
      simpa using hN (2 * n + 1) (by omega)
  · rintro ⟨ha, hb⟩ ε hε
    obtain ⟨Na, hNa⟩ := ha ε hε
    obtain ⟨Nb, hNb⟩ := hb ε hε
    refine ⟨2 * max Na Nb, fun n hn => ?_⟩
    have hna : Na ≤ n / 2 := by omega
    have hnb : Nb ≤ n / 2 := by omega
    change dist (if (Nat.divModEquiv 2 n).2 = 0 then a (n / 2) else b (n / 2)) 0 < ε
    split_ifs
    · exact hNa _ hna
    · exact hNb _ hnb

def CircleNullRel (x y : ℕ → UnitAddCircle) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

def RealNullRel (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n - y n) atTop (𝓝 0)

theorem circle_real_null_reduction (x y : ℕ → UnitAddCircle) :
    CircleNullRel x y ↔ RealNullRel (realEmbed x) (realEmbed y) := by
  rw [CircleNullRel, null_circle_iff_complex]
  change _ ↔ Tendsto (realEmbed x - realEmbed y) atTop (𝓝 0)
  rw [realEmbed, realEmbed, interleave_sub, null_interleave]
  constructor
  · intro h
    constructor
    · change Tendsto (fun n => (circleEmbed (x n)).re - (circleEmbed (y n)).re) atTop (𝓝 0)
      simpa only [Function.comp_def, Complex.sub_re, Complex.zero_re] using
        Complex.continuous_re.continuousAt.tendsto.comp h
    · change Tendsto (fun n => (circleEmbed (x n)).im - (circleEmbed (y n)).im) atTop (𝓝 0)
      simpa only [Function.comp_def, Complex.sub_im, Complex.zero_im] using
        Complex.continuous_im.continuousAt.tendsto.comp h
  · rintro ⟨hr, hi⟩
    apply tendsto_zero_iff_norm_tendsto_zero.2
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => Complex.norm_le_abs_re_add_abs_im _)
    simpa using hr.norm.add hi.norm

/-- The concrete cos/sin interleaving reduces the real-exponent summability relations. -/
theorem circle_real_lp_reduction_real (p : ℝ) (hp : 1 ≤ p)
    (x y : ℕ → UnitAddCircle) :
    (Summable fun n => ‖x n - y n‖ ^ p) ↔
    Summable (fun n => |realEmbed x n - realEmbed y n| ^ p) := by
  have hp0 : 0 ≤ p := by linarith
  have hpt : 0 < (ENNReal.ofReal p).toReal := by
    rw [ENNReal.toReal_ofReal hp0]
    linarith
  simpa only [CircleLpRel, RealLpRel, memℓp_gen_iff hpt,
    ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using
    circle_real_lp_reduction (ENNReal.ofReal p) hpt x y

/-- A single continuous map works for every finite real exponent p >= 1 and for c0. -/
theorem compact_circle_reductions :
    ∃ b : (ℕ → UnitAddCircle) → (ℕ → ℝ), Continuous b ∧
      (∀ p : ℝ, 1 ≤ p → ∀ x y,
        (Summable fun n => ‖x n - y n‖ ^ p) ↔
        Summable (fun n => |b x n - b y n| ^ p)) ∧
      (∀ x y, Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
        Tendsto (fun n => b x n - b y n) atTop (𝓝 0)) := by
  exact ⟨realEmbed, continuous_realEmbed, circle_real_lp_reduction_real,
    circle_real_null_reduction⟩


end MeasureEquivalenceCircleReduction
end
end MainProofScope28

/- Source module: CirclePresentation -/
section MainProofScope29
open Filter Topology Set TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCirclePresentation

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

def hpInclusion (p : ℝ≥0∞) : Hp p →+ K where
  toFun h := h
  map_zero' := rfl
  map_add' _ _ := rfl

lemma hpInclusion_injective (p : ℝ≥0∞) : Function.Injective (hpInclusion p) := by
  intro x y h
  apply lp.ext
  exact h

lemma hpInclusion_continuous (p : ℝ≥0∞) [Fact (1 ≤ p)] : Continuous (hpInclusion p) :=
  continuous_hp_coordinates p

def hpImage (p : ℝ≥0∞) : AddSubgroup K := (hpInclusion p).range

@[simp] lemma mem_hpImage_iff (p : ℝ≥0∞) (x : K) :
    x ∈ hpImage p ↔ Memℓp x p := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

def h0Inclusion : H0 →+ K where
  toFun h := (h : Hp ⊤)
  map_zero' := rfl
  map_add' _ _ := rfl

lemma h0Inclusion_injective : Function.Injective h0Inclusion := by
  intro x y h
  apply Subtype.ext
  apply lp.ext
  exact h

lemma h0Inclusion_continuous : Continuous h0Inclusion := continuous_h0_coordinates

def h0Image : AddSubgroup K := h0Inclusion.range

lemma memlp_top (x : K) : Memℓp x ⊤ := by
  apply memℓp_infty
  refine ⟨1 / 2, ?_⟩
  rintro a ⟨i, rfl⟩
  simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := x i) (by norm_num)

@[simp] lemma mem_h0Image_iff (x : K) :
    x ∈ h0Image ↔ Tendsto x atTop (𝓝 0) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact h.property
  · intro hx
    exact ⟨⟨⟨x, memlp_top x⟩, hx⟩, rfl⟩

open MeasureEquivalenceCircleReduction

theorem hp_coset_real_iff (p : ℝ≥0∞) (hp : 0 < p.toReal) (x y : K) :
    x - y ∈ hpImage p ↔ RealLpRel p (realEmbed x) (realEmbed y) := by
  rw [mem_hpImage_iff]
  exact circle_real_lp_reduction p hp x y

theorem h0_coset_real_iff (x y : K) :
    x - y ∈ h0Image ↔ RealNullRel (realEmbed x) (realEmbed y) := by
  rw [mem_h0Image_iff]
  exact circle_real_null_reduction x y

theorem hp_compose_reduction {Y : Type*} (R : Y → Y → Prop)
    (p : ℝ≥0∞) (hp : 0 < p.toReal) (f : (ℕ → ℝ) → Y)
    (hf : ∀ x y, RealLpRel p x y ↔ R (f x) (f y)) (x y : K) :
    x - y ∈ hpImage p ↔ R (f (realEmbed x)) (f (realEmbed y)) :=
  (hp_coset_real_iff p hp x y).trans (hf _ _)

theorem h0_compose_reduction {Y : Type*} (R : Y → Y → Prop)
    (f : (ℕ → ℝ) → Y)
    (hf : ∀ x y, RealNullRel x y ↔ R (f x) (f y)) (x y : K) :
    x - y ∈ h0Image ↔ R (f (realEmbed x)) (f (realEmbed y)) :=
  (h0_coset_real_iff x y).trans (hf _ _)

end MeasureEquivalenceCirclePresentation
end
end MainProofScope29

/- Source module: TailGraphObstruction -/
section MainProofScope30
/-! Direct obstruction for the graph (coordinate inclusion, Hilbert feature).
This avoids adding the weighted character embedding to the Hilbert feature. -/

open Filter Topology Set
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceTail

open MeasureEquivalenceTorus MeasureEquivalenceGrid MeasureEquivalenceCircle

variable {H E : Type*} [NormedAddCommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma graph_long_bound (coord : H → ℕ → UnitAddCircle) (hzero : coord 0 = 0)
    (r : H → E) (hg : IsInducing (fun h => (coord h, r h))) :
    ∃ (N : ℕ) (c : ℝ), 0 < c ∧ ∀ h,
      (∀ k < N, coord h k = 0) → (1 / 4 : ℝ) ≤ ‖h‖ → c ≤ ‖r h - r 0‖ := by
  have hball : Metric.ball (0 : H) (1 / 4) ∈ 𝓝 (0 : H) :=
    Metric.ball_mem_nhds _ (by norm_num)
  rw [hg.nhds_eq_comap 0, Filter.mem_comap] at hball
  obtain ⟨s, hs, hsub⟩ := hball
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hs
  rw [hzero, nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, t, ht, htU⟩ := hU
  obtain ⟨c, hc, hcV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨I.sup id + 1, c, hc, fun h htail hnorm => ?_⟩
  by_contra! hsmall
  have hcoord : coord h ∈ U := htU (by
    intro k hk
    have hkbound : k ≤ I.sup id := Finset.le_sup (f := id) hk
    rw [htail k (by omega)]
    exact mem_of_mem_nhds (ht k))
  have hr : r h ∈ V := hcV (by simpa [Metric.mem_ball, dist_eq_norm] using hsmall)
  have hh : h ∈ Metric.ball (0 : H) (1 / 4) := hsub (hUV ⟨hcoord, hr⟩)
  have : ‖h‖ < (1 / 4 : ℝ) := by simpa [Metric.mem_ball] using hh
  linarith

theorem no_invariant_hilbert_graph
    (coord : H → ℕ → UnitAddCircle) (hzero : coord 0 = 0)
    (hgrids : ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ H),
      (∀ x k, k < N → coord (g x) k = 0) ∧
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ))
    (r : H → E) (hg : IsEmbedding (fun h => (coord h, r h)))
    (hinv : ∀ h k t, ‖r (h + t) - r (k + t)‖ = ‖r h - r k‖) : False := by
  obtain ⟨N, c, hc, hlong⟩ := graph_long_bound coord hzero r hg.isInducing
  have hr : Continuous r := continuous_snd.comp hg.continuous
  obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousAt_iff.mp
    (hr.continuousAt (x := 0)) (c / 3) (by positivity)
  obtain ⟨m, hm, g, htail, hglong, hgshort⟩ := hgrids N δ hδ
  letI : NeZero m := ⟨by omega⟩
  have hdisp (x y : Fin (m ^ 2) → ZMod m) :
      ‖r (g (x + y)) - r (g x)‖ = ‖r (g y) - r 0‖ := by
    rw [map_add, add_comm (g x) (g y)]
    simpa only [zero_add] using hinv (g y) 0 (g x)
  apply finite_grid_gap hm (r ∘ g) c hc
  · intro j x
    simpa only [Function.comp_apply, hdisp] using
      hlong _ (htail _) (hglong j)
  · intro ε x
    rw [Function.comp_apply, Function.comp_apply, hdisp]
    apply le_of_lt
    simpa only [dist_eq_norm] using hsmall
      (show dist (g (shortShift ε)) 0 < δ by simpa using hgshort ε)

variable (N : ℕ) {m n : ℕ}

/-- Insert N leading zero residues. -/
def pad : (Fin n → ZMod m) →+ (Fin (N + n) → ZMod m) where
  toFun x j := if hj : N ≤ j.val then x ⟨j.val - N, by omega⟩ else 0
  map_zero' := by ext j; simp
  map_add' x y := by ext j; simp only [Pi.add_apply]; split_ifs <;> simp

def padSigns (ε : Fin n → Fin 3) (j : Fin (N + n)) : Fin 3 :=
  if hj : N ≤ j.val then ε ⟨j.val - N, by omega⟩ else 1

lemma pad_short (ε : Fin n → Fin 3) :
    pad N (shortShift (m := m) ε) = shortShift (padSigns N ε) := by
  ext j
  simp only [pad, AddMonoidHom.coe_mk, ZeroHom.coe_mk, shortShift, padSigns]
  split_ifs <;> simp [step]

lemma pad_axis (j : Fin n) (a : ZMod m) :
    pad N (axisHom j a) = axisHom (⟨N + j.val, by omega⟩ : Fin (N + n)) a := by
  ext i
  simp only [pad, AddMonoidHom.coe_mk, ZeroHom.coe_mk, axisHom]
  by_cases hi : N ≤ i.val
  · rw [dif_pos hi]
    congr 1
    apply propext
    simp only [Fin.ext_iff]
    omega
  · rw [dif_neg hi]
    have hne : i ≠ (⟨N + j.val, by omega⟩ : Fin (N + n)) := by
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_mk] at this
      omega
    simp [hne]

variable (p : ℝ≥0∞) [NeZero m]

def tailGrid : (Fin n → ZMod m) →+ Hp p := (grid p).comp (pad N)

def tailGrid0 : (Fin n → ZMod m) →+ H0 := grid0.comp (pad N)

lemma tailGrid_zero (x : Fin n → ZMod m) {k : ℕ} (hk : k < N) :
    tailGrid N p x k = 0 := by
  simp [tailGrid, gridValue, pad, show k < N + n by omega, show ¬ N ≤ k by omega]

lemma tailGrid0_zero (x : Fin n → ZMod m) {k : ℕ} (hk : k < N) :
    ((tailGrid0 N x : H0) : Hp ⊤) k = 0 := tailGrid_zero N ⊤ x hk

lemma tailGrid_long (hp : p ≠ 0) (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖tailGrid N p (axisHom j ((m / 2 : ℕ) : ZMod m))‖ := by
  change (1 / 4 : ℝ) ≤ ‖grid p (pad N (axisHom j ((m / 2 : ℕ) : ZMod m)))‖
  rw [pad_axis]
  exact grid_long_bound p hp heven _

lemma tailGrid0_long (heven : Even m) (j : Fin n) :
    (1 / 4 : ℝ) ≤ ‖tailGrid0 N (axisHom j ((m / 2 : ℕ) : ZMod m))‖ :=
  tailGrid_long N ⊤ (by simp) heven j

lemma tailGrid_short_rpow (hp : 0 < p.toReal) (ε : Fin n → Fin 3) :
    ‖tailGrid (m := m) N p (shortShift ε)‖ ^ p.toReal ≤
      ((N + n : ℕ) : ℝ) * (1 / (m : ℝ)) ^ p.toReal := by
  change ‖grid p (pad N (shortShift ε))‖ ^ p.toReal ≤ _
  rw [pad_short]
  exact grid_short_rpow p hp _

lemma tailGrid0_short (ε : Fin n → Fin 3) :
    ‖tailGrid0 (m := m) N (shortShift ε)‖ ≤ 1 / (m : ℝ) := by
  change ‖grid0 (pad N (shortShift ε))‖ ≤ _
  rw [pad_short]
  exact grid0_short_bound _

lemma tailGrid_square_short_rpow (hp : 0 < p.toReal) (hm : 2 ≤ m) (hNm : N ≤ m)
    (ε : Fin (m ^ 2) → Fin 3) :
    ‖tailGrid (m := m) N p (shortShift ε)‖ ^ p.toReal ≤
      2 * (m : ℝ) ^ (2 - p.toReal) := by
  have hmreal : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hNreal : (N : ℝ) ≤ m := by exact_mod_cast hNm
  have hsum : ((N + m ^ 2 : ℕ) : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have heq : (m : ℝ) ^ 2 * (1 / (m : ℝ)) ^ p.toReal =
      (m : ℝ) ^ (2 - p.toReal) := by
    rw [Real.rpow_sub (by linarith : (0 : ℝ) < m), Real.rpow_two]
    simp [one_div, Real.inv_rpow, div_eq_mul_inv]
  calc
    _ ≤ ((N + m ^ 2 : ℕ) : ℝ) * (1 / (m : ℝ)) ^ p.toReal :=
      tailGrid_short_rpow N p hp ε
    _ ≤ (2 * (m : ℝ) ^ 2) * (1 / (m : ℝ)) ^ p.toReal :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = 2 * (m : ℝ) ^ (2 - p.toReal) := by rw [mul_assoc, heq]

lemma exists_even_rpow_small_ge {r δ : ℝ} (hr : r < 0) (hδ : 0 < δ) :
    ∃ m : ℕ, 2 ≤ m ∧ N ≤ m ∧ Even m ∧ (m : ℝ) ^ r < δ := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ) ^ r) atTop (𝓝 0) := by
    simpa only [neg_neg, Function.comp_def] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hr)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hδ))
  refine ⟨2 * (N + K + 1), by omega, by omega,
    ⟨N + K + 1, by omega⟩, hK _ (by omega)⟩

def hpCoordinates (x : Hp p) : ℕ → UnitAddCircle := x

def h0Coordinates (x : H0) : ℕ → UnitAddCircle := (x : Hp ⊤)

theorem H0_has_small_tail_grids :
    ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ H0),
      (∀ x k, k < N → h0Coordinates (g x) k = 0) ∧
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro N δ hδ
  obtain ⟨m, hm, _hNm, heven, hsmall⟩ :=
    exists_even_rpow_small_ge N (r := -1) (by norm_num) hδ
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, tailGrid0 N, fun x k hk => tailGrid0_zero N x hk,
    tailGrid0_long N heven, fun ε => ?_⟩
  apply (tailGrid0_short N ε).trans_lt
  simpa [Real.rpow_neg_one, one_div] using hsmall

theorem Hp_has_small_tail_grids [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ (m : ℕ) (_hm : 2 ≤ m)
      (g : (Fin (m ^ 2) → ZMod m) →+ Hp p),
      (∀ x k, k < N → hpCoordinates p (g x) k = 0) ∧
      (∀ j, (1 / 4 : ℝ) ≤ ‖g (axisHom j ((m / 2 : ℕ) : ZMod m))‖) ∧
      (∀ ε, ‖g (shortShift ε)‖ < δ) := by
  intro N δ hδ
  have hp0 : 0 < p.toReal := by linarith
  have hpn : p ≠ 0 := by intro hz; norm_num [hz] at hp
  have hδp : 0 < δ ^ p.toReal := Real.rpow_pos_of_pos hδ p.toReal
  obtain ⟨m, hm, hNm, heven, hsmall⟩ :=
    exists_even_rpow_small_ge N (r := 2 - p.toReal) (δ := δ ^ p.toReal / 2)
      (by linarith) (by positivity)
  letI : NeZero m := ⟨by omega⟩
  refine ⟨m, hm, tailGrid N p, fun x k hk => tailGrid_zero N p x hk,
    tailGrid_long N p hpn heven, fun ε => ?_⟩
  apply (Real.rpow_lt_rpow_iff (norm_nonneg _) hδ.le hp0).mp
  apply (tailGrid_square_short_rpow N p hp0 hm hNm ε).trans_lt
  linarith

/-- No embedding of the coordinate/density graph for actual H0, when only
the Hilbert feature distance is assumed invariant. -/
theorem no_H0_invariant_hilbert_graph (r : H0 → E)
    (hg : IsEmbedding (fun h => (h0Coordinates h, r h)))
    (hinv : ∀ h k t, ‖r (h + t) - r (k + t)‖ = ‖r h - r k‖) : False :=
  no_invariant_hilbert_graph h0Coordinates rfl H0_has_small_tail_grids r hg hinv

/-- The corresponding graph obstruction for actual Hp, finite p>2. The
ambient coordinate space carries its product topology. -/
theorem no_Hp_invariant_hilbert_graph [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (r : Hp p → E) (hg : IsEmbedding (fun h => (hpCoordinates p h, r h)))
    (hinv : ∀ h k t, ‖r (h + t) - r (k + t)‖ = ‖r h - r k‖) : False :=
  no_invariant_hilbert_graph (hpCoordinates p) rfl (Hp_has_small_tail_grids p hp) r hg hinv

end MeasureEquivalenceTail
end
end MainProofScope30

/- Source module: NegativeReduction -/
section MainProofScope31
/-! Actual negative Borel-reducibility statements, assembled from the
compact probability kernel, concrete RN graph, and concrete circle grids. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceNegative

open MeasureEquivalenceResearch MeasureEquivalenceCompactAveraging
open MeasureEquivalenceRNGraph MeasureEquivalenceRNPresentation MeasureEquivalenceHellinger
open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology
open MeasureEquivalenceCirclePresentation MeasureEquivalenceCircleReduction
open MeasureEquivalenceTail

variable {Y : Type*} [TopologicalSpace Y] [PolishSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem c0_reduction_impossible (f : (ℕ → ℝ) → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, RealNullRel x y ↔
      EquivalentMeasures (f x : Measure Y) (f y : Measure Y)) : False := by
  let : PolishSpace (Multiplicative K) := inferInstanceAs (PolishSpace K)
  let := upgradeIsCompletelyMetrizable (Multiplicative K)
  let := baseTranslationAction K Y
  let := continuous_baseTranslationAction K Y
  let := h0_polish
  let : PolishSpace (Multiplicative H0) := inferInstanceAs (PolishSpace H0)
  let : MeasurableSpace (Multiplicative H0) := borel (Multiplicative H0)
  let : BorelSpace (Multiplicative H0) := ⟨rfl⟩
  let F : K → ProbabilityMeasure Y := f ∘ realEmbed
  have hF : Measurable F := hf.comp continuous_realEmbed.measurable
  have hFred : ∀ x y, EquivalentMeasures (F x : Measure Y) (F y : Measure Y) ↔
      x - y ∈ h0Image := by
    intro x y
    exact (h0_compose_reduction (fun μ ν : ProbabilityMeasure Y =>
      EquivalentMeasures (μ : Measure Y) (ν : Measure Y)) f hred x y).symm
  obtain ⟨M, hM, hMQ⟩ := torus_polish_action_averaging h0Image F hF hFred
  let := hM
  let i : Multiplicative H0 →* Multiplicative K :=
    AddMonoidHom.toMultiplicative h0Inclusion
  have hi : Continuous i := h0Inclusion_continuous
  have hinj : Function.Injective i := h0Inclusion_injective
  have hrange : Set.range i = (quasiInvariantSubgroup (K := Multiplicative K) M : Set _) := by
    ext g
    have hqi : g ∈ quasiInvariantSubgroup (K := Multiplicative K) M ↔ g.toAdd ∈ h0Image :=
      (mem_quasiInvariantSubgroup_iff M g).trans (hMQ g)
    change g ∈ Set.range i ↔ g ∈ quasiInvariantSubgroup (K := Multiplicative K) M
    rw [hqi]
    rfl
  let r : H0 → Lp ℝ 2 M := fun h => root (orbit M (i (Multiplicative.ofAdd h)) : Measure _) M
  have he := rn_graph_embedding M i hi hinj hrange
  have he' : Topology.IsEmbedding (fun h : H0 => (h0Coordinates h, r h)) := he
  apply no_H0_invariant_hilbert_graph r he'
  intro h k t
  have hd := rn_distance_invariant M i hrange
    (Multiplicative.ofAdd t) (Multiplicative.ofAdd h) (Multiplicative.ofAdd k)
  change dist (r (t + h)) (r (t + k)) = dist (r h) (r k) at hd
  simpa only [add_comm t h, add_comm t k, dist_eq_norm] using hd

theorem c0_not_borel_reducible :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, RealNullRel x y ↔ EquivalentMeasures (f x : Measure Y) (f y : Measure Y) := by
  rintro ⟨f, hf, hred⟩
  exact c0_reduction_impossible f hf hred

theorem lp_reduction_impossible (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal)
    (f : (ℕ → ℝ) → ProbabilityMeasure Y) (hf : Measurable f)
    (hred : ∀ x y, RealLpRel p x y ↔
      EquivalentMeasures (f x : Measure Y) (f y : Measure Y)) : False := by
  let : PolishSpace (Multiplicative K) := inferInstanceAs (PolishSpace K)
  let := upgradeIsCompletelyMetrizable (Multiplicative K)
  let := baseTranslationAction K Y
  let := continuous_baseTranslationAction K Y
  have hpfin : p ≠ ⊤ := by intro h; norm_num [h] at hp
  let := hp_polish p hpfin
  let : PolishSpace (Multiplicative (Hp p)) := inferInstanceAs (PolishSpace (Hp p))
  let : MeasurableSpace (Multiplicative (Hp p)) := borel (Multiplicative (Hp p))
  let : BorelSpace (Multiplicative (Hp p)) := ⟨rfl⟩
  let F : K → ProbabilityMeasure Y := f ∘ realEmbed
  have hF : Measurable F := hf.comp continuous_realEmbed.measurable
  have hFred : ∀ x y, EquivalentMeasures (F x : Measure Y) (F y : Measure Y) ↔
      x - y ∈ hpImage p := by
    intro x y
    exact (hp_compose_reduction (fun μ ν : ProbabilityMeasure Y =>
      EquivalentMeasures (μ : Measure Y) (ν : Measure Y)) p (by linarith) f hred x y).symm
  obtain ⟨M, hM, hMQ⟩ := torus_polish_action_averaging (hpImage p) F hF hFred
  let := hM
  let i : Multiplicative (Hp p) →* Multiplicative K :=
    AddMonoidHom.toMultiplicative (hpInclusion p)
  have hi : Continuous i := hpInclusion_continuous p
  have hinj : Function.Injective i := hpInclusion_injective p
  have hrange : Set.range i = (quasiInvariantSubgroup (K := Multiplicative K) M : Set _) := by
    ext g
    have hqi : g ∈ quasiInvariantSubgroup (K := Multiplicative K) M ↔ g.toAdd ∈ hpImage p :=
      (mem_quasiInvariantSubgroup_iff M g).trans (hMQ g)
    change g ∈ Set.range i ↔ g ∈ quasiInvariantSubgroup (K := Multiplicative K) M
    rw [hqi]
    rfl
  let r : Hp p → Lp ℝ 2 M := fun h => root (orbit M (i (Multiplicative.ofAdd h)) : Measure _) M
  have he := rn_graph_embedding M i hi hinj hrange
  have he' : Topology.IsEmbedding (fun h : Hp p => (hpCoordinates p h, r h)) := he
  apply no_Hp_invariant_hilbert_graph p hp r he'
  intro h k t
  have hd := rn_distance_invariant M i hrange
    (Multiplicative.ofAdd t) (Multiplicative.ofAdd h) (Multiplicative.ofAdd k)
  change dist (r (t + h)) (r (t + k)) = dist (r h) (r k) at hd
  simpa only [add_comm t h, add_comm t k, dist_eq_norm] using hd

theorem lp_not_borel_reducible (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p.toReal) :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, RealLpRel p x y ↔ EquivalentMeasures (f x : Measure Y) (f y : Measure Y) := by
  rintro ⟨f, hf, hred⟩
  exact lp_reduction_impossible p hp f hf hred

/-- The negative statement with an ordinary finite real exponent and the
usual explicit summability definition, without ENNReal or lp notation. -/
theorem lp_summability_not_borel_reducible (p : ℝ) (hp : 2 < p) :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, (Summable fun n => |x n - y n| ^ p) ↔
        EquivalentMeasures (f x : Measure Y) (f y : Measure Y) := by
  have hp0 : 0 ≤ p := by linarith
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by positivity)]
    linarith⟩
  have hpt : 2 < (ENNReal.ofReal p).toReal := by simpa [ENNReal.toReal_ofReal hp0]
  rintro ⟨f, hf, hred⟩
  apply lp_reduction_impossible (ENNReal.ofReal p) hpt f hf
  intro x y
  simpa only [RealLpRel, memℓp_gen_iff (show 0 < (ENNReal.ofReal p).toReal by linarith),
    ENNReal.toReal_ofReal hp0, Real.norm_eq_abs] using hred x y

/-- The null-sequence statement written without auxiliary relation notation. -/
theorem null_difference_not_borel_reducible :
    ¬ ∃ f : (ℕ → ℝ) → ProbabilityMeasure Y, Measurable f ∧
      ∀ x y, Tendsto (fun n => x n - y n) atTop (𝓝 0) ↔
        ((f x : Measure Y) ≪ f y ∧ (f y : Measure Y) ≪ f x) :=
  c0_not_borel_reducible

end MeasureEquivalenceNegative
end
end MainProofScope31

open MeasureTheory Filter MeasureEquivalenceMission
open scoped Topology

theorem solution (p : ℝ) (hp : 1 ≤ p) :
    BorelReducesToMeasureEquivalence (LpDifference p) ↔ p ≤ 2 := by
  letI : PolishSpace (ℕ → Bool) := by constructor <;> infer_instance
  constructor
  · intro h
    by_contra! hp2
    exact MeasureEquivalenceNegative.lp_summability_not_borel_reducible
      (Y := ℕ → Bool) p hp2 h
  · intro hp2
    obtain ⟨f, _hc, hf, hred⟩ :=
      MeasureEquivalenceGaussian.exists_continuous_gaussian_reduction_one_le p hp hp2
    obtain ⟨g, hg, hiff⟩ :=
      MeasureEquivalenceSampleSpace.transfer_real_sequence_reduction_to_cantor
        (fun x y : ℕ → ℝ => Summable (fun n => |x n - y n| ^ p)) f hf hred
    exact ⟨g, hg, hiff⟩

#print axioms solution
