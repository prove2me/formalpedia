-- Prove2me | solution 1 for MeasureEquivalenceMission.c0_not_reducible
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-24T02:51:33.539981+00:00
-- url     : https://prove2.me/submissions/47fa13d0-87b8-430b-a1db-4d1c92f68a3b

import Definitions.Def_MeasureEquivalenceSequences
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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

/- Source module: KernelEquivalence -/
section MainProofScope0
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
end MainProofScope0

/- Source module: CompactAveraging -/
section MainProofScope1
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
end MainProofScope1

/- Source module: DensitySquare -/
section MainProofScope2
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
end MainProofScope2

/- Source module: DensityMeasure -/
section MainProofScope3
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
end MainProofScope3

/- Source module: HellingerTransport -/
section MainProofScope4
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
end MainProofScope4

/- Source module: DensityGraphCompleteness -/
section MainProofScope5
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
end MainProofScope5

/- Source module: PolishGroupTopology -/
section MainProofScope6
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
end MainProofScope6

/- Source module: RNGraph -/
section MainProofScope7
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
end MainProofScope7

/- Source module: InvariantGraphGroup -/
section MainProofScope8
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
end MainProofScope8

/- Source module: RNPresentation -/
section MainProofScope9
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
end MainProofScope9

/- Source module: FiniteFourier -/
section MainProofScope10
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
end MainProofScope10

/- Source module: ScalarMultiplier -/
section MainProofScope11
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
end MainProofScope11

/- Source module: TrigMultiplier -/
section MainProofScope12
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
end MainProofScope12

/- Source module: FiniteTorus -/
section MainProofScope13
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
end MainProofScope13

/- Source module: GridObstruction -/
section MainProofScope14
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
end MainProofScope14

/- Source module: CircleGrids -/
section MainProofScope15
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
end MainProofScope15

/- Source module: CircleTopology -/
section MainProofScope16
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
end MainProofScope16

/- Source module: CircleReduction -/
section MainProofScope17
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
end MainProofScope17

/- Source module: CirclePresentation -/
section MainProofScope18
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
end MainProofScope18

/- Source module: TailGraphObstruction -/
section MainProofScope19
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
end MainProofScope19

/- Source module: NegativeReduction -/
section MainProofScope20
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
end MainProofScope20

open MeasureTheory Filter MeasureEquivalenceMission
open scoped Topology

theorem solution : ¬ BorelReducesToMeasureEquivalence NullDifference := by
  letI : PolishSpace (ℕ → Bool) := by constructor <;> infer_instance
  exact MeasureEquivalenceNegative.null_difference_not_borel_reducible (Y := ℕ → Bool)

#print axioms solution
