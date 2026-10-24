-- Prove2me | solution 1 for MeasureEquivalenceMission.classical_positive
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-24T02:13:01.246535+00:00
-- url     : https://prove2.me/submissions/dc2092eb-94d5-4392-acdb-b761e685f047

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

/- Source module: gaussian/GaussianFinite.lean -/
section PortScope0
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
end PortScope0

/- Source module: gaussian/DensitySquare.lean -/
section PortScope1
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
end PortScope1

/- Source module: gaussian/DensityExtension.lean -/
section PortScope2
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
end PortScope2

/- Source module: gaussian/ProductAffinity.lean -/
section PortScope3
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
end PortScope3

/- Source module: gaussian/GaussianCriterion.lean -/
section PortScope4
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
end PortScope4

/- Source module: gaussian/GaussianContinuity.lean -/
section PortScope5
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
end PortScope5

/- Source module: gaussian/GaussianCanonical.lean -/
section PortScope6
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
end PortScope6

/- Source module: HilbertCoordinates.lean -/
section PortScope7
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
end PortScope7

/- Source module: SnowflakeIntegral.lean -/
section PortScope8
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
end PortScope8

/- Source module: SnowflakeReduction.lean -/
section PortScope9
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
end PortScope9

/- Source module: GaussianPositive.lean -/
section PortScope10
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
end PortScope10

/- Source module: SampleSpaceTransport.lean -/
section PortScope11
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
end PortScope11

open MeasureTheory MeasureEquivalenceMission

theorem solution (p : ℝ) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    BorelReducesToMeasureEquivalence (LpDifference p) := by
  obtain ⟨f, _hc, hf, hred⟩ :=
    MeasureEquivalenceGaussian.exists_continuous_gaussian_reduction_one_le p hp hp2
  obtain ⟨g, hg, hiff⟩ :=
    MeasureEquivalenceSampleSpace.transfer_real_sequence_reduction_to_cantor
      (fun x y : ℕ → ℝ => Summable (fun n => |x n - y n| ^ p)) f hf hred
  exact ⟨g, hg, hiff⟩

#print axioms solution
