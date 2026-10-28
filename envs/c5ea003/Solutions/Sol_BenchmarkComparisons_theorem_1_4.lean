-- Prove2me | solution 1 for BenchmarkComparisons.theorem_1_4
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T09:54:14.230767+00:00
-- url     : https://prove2.me/submissions/dfb7dd79-ec35-4d38-86f3-2c698acf87fe

import Definitions.Def_BenchmarkRelations
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Order.Filter.CountableInter
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Theorems.Thm_BenchmarkComparisons_c0_jump_obstruction


/- Preserved source skeleton: ClopenHaarNode -/
namespace BenchmarkJumpSubmission
section Source0
/-! Concrete varying-measure Haar nodes for a positive clopen split.
The node is (b 1_A - a 1_B)/sqrt(a*b*(a+b)), algebraically equal to
the coefficients displayed in Benchmark.tex. -/

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

variable {α : Type*} [MeasurableSpace α]

def splitHaar (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) : Lp ℝ 2 μ :=
  (Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)))⁻¹ •
    ((μ.real B) • indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) -
      (μ.real A) • indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ))

theorem splitHaar_norm (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (ha : 0 < μ.real A) (hb : 0 < μ.real B) :
    ‖splitHaar μ A B hA hB‖ = 1 := by
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  have hff : inner ℝ f f = μ.real A := by
    simpa only [f, inter_self] using
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hA hA
  have hgg : inner ℝ g g = μ.real B := by
    simpa only [g, inter_self] using
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hB hB
  have hfg : inner ℝ f g = 0 := by
    simpa only [f, g, disjoint_iff_inter_eq_empty.mp hAB, measureReal_empty] using
      L2.real_inner_indicatorConstLp_one_indicatorConstLp_one hA hB
  have hgf : inner ℝ g f = 0 := by rw [real_inner_comm, hfg]
  have hsq : ‖μ.real B • f - μ.real A • g‖ ^ 2 =
      μ.real A * μ.real B * (μ.real A + μ.real B) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, hff, hgg, hfg, hgf]
    ring
  have hpos : 0 < μ.real A * μ.real B * (μ.real A + μ.real B) := by positivity
  have hroot : 0 < Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)) :=
    Real.sqrt_pos.mpr hpos
  have hnorm : ‖μ.real B • f - μ.real A • g‖ =
      Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)) := by
    nlinarith [Real.sq_sqrt hpos.le, norm_nonneg (μ.real B • f - μ.real A • g)]
  change ‖(Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)))⁻¹ •
    (μ.real B • f - μ.real A • g)‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot), hnorm,
    inv_mul_cancel₀ hroot.ne']

theorem splitHaar_inner_one (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    inner ℝ (splitHaar μ A B hA hB)
      (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℝ)) = 0 := by
  unfold splitHaar
  simp only [inner_smul_left, inner_sub_left, RCLike.conj_to_real,
    L2.real_inner_indicatorConstLp_one_indicatorConstLp_one, inter_univ]
  ring

section Topology

variable [TopologicalSpace α] [CompactSpace α] [BorelSpace α]

theorem continuous_clopen_mass (A : Set α) (hA : IsClopen A) :
    Continuous (fun μ : ProbabilityMeasure α => (μ : Measure α).real A) := by
  let f : C(α, ℝ) := ⟨A.indicator (fun _ => 1), hA.continuous_indicator continuous_const⟩
  have hcont := ProbabilityMeasure.continuous_integral_continuousMap f
  have heq : (fun μ : ProbabilityMeasure α => ∫ x, f x ∂(μ : Measure α)) =
      (fun μ : ProbabilityMeasure α => (μ : Measure α).real A) := by
    funext μ
    exact integral_indicator_one hA.isClosed.measurableSet
  rwa [heq] at hcont

def PositiveSplitProbabilities (A B : Set α) : Set (ProbabilityMeasure α) :=
  {μ | 0 < (μ : Measure α).real A ∧ 0 < (μ : Measure α).real B}



def haarNodeFunction (A B : Set α) (μ : ProbabilityMeasure α) (x : α) : ℝ :=
  ((μ : Measure α).real B * A.indicator (fun _ => (1 : ℝ)) x -
    (μ : Measure α).real A * B.indicator (fun _ => (1 : ℝ)) x) /
      Real.sqrt ((μ : Measure α).real A * (μ : Measure α).real B *
        ((μ : Measure α).real A + (μ : Measure α).real B))

/-- Finite Haar node values depend jointly continuously on the weak measure
parameter and the underlying point, on the genuine positive-mass locus. -/
theorem continuous_haarNodeFunction (A B : Set α) (hA : IsClopen A) (hB : IsClopen B) :
    Continuous (fun p : PositiveSplitProbabilities A B × α =>
      haarNodeFunction A B p.1 p.2) := by
  have ha : Continuous (fun μ : PositiveSplitProbabilities A B =>
      ((μ : ProbabilityMeasure α) : Measure α).real A) :=
    (continuous_clopen_mass A hA).comp continuous_subtype_val
  have hb : Continuous (fun μ : PositiveSplitProbabilities A B =>
      ((μ : ProbabilityMeasure α) : Measure α).real B) :=
    (continuous_clopen_mass B hB).comp continuous_subtype_val
  unfold haarNodeFunction
  apply Continuous.div
  · exact ((hb.comp continuous_fst).mul
      ((hA.continuous_indicator continuous_const).comp continuous_snd)).sub
      ((ha.comp continuous_fst).mul
        ((hB.continuous_indicator continuous_const).comp continuous_snd))
  · exact (((ha.mul hb).mul (ha.add hb)).sqrt).comp continuous_fst
  · intro p
    apply (Real.sqrt_pos.mpr ?_).ne'
    have hpa := p.1.property.1
    have hpb := p.1.property.2
    positivity




end Topology
end BenchmarkJump
end
end Source0
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarCylinders -/
namespace BenchmarkJumpSubmission
section Source1
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

abbrev HaarCantor := ℕ → Bool
abbrev HaarNodeIndex := Σ n : ℕ, Fin n → Bool

def prefixCylinder {n : ℕ} (s : Fin n → Bool) : Set HaarCantor :=
  {x | ∀ i : Fin n, x i = s i}

theorem isClopen_prefixCylinder {n : ℕ} (s : Fin n → Bool) :
    IsClopen (prefixCylinder s) := by
  change IsClopen {x : HaarCantor | ∀ i : Fin n, x i = s i}
  simp only [setOf_forall]
  apply isClopen_iInter_of_finite
  intro i
  exact (isClopen_discrete ({s i} : Set Bool)).preimage (continuous_apply (i : ℕ))

theorem prefixCylinder_nonempty {n : ℕ} (s : Fin n → Bool) :
    (prefixCylinder s).Nonempty := by
  let x : HaarCantor := fun i => if hi : i < n then s ⟨i, hi⟩ else false
  refine ⟨x, ?_⟩
  intro i
  simp [x, i.isLt]

theorem prefixCylinder_zero (s : Fin 0 → Bool) : prefixCylinder s = univ := by
  ext x
  simp [prefixCylinder]

theorem mem_prefixCylinder_snoc {n : ℕ} (s : Fin n → Bool) (b : Bool) (x : HaarCantor) :
    x ∈ prefixCylinder (Fin.snoc s b) ↔ x ∈ prefixCylinder s ∧ x n = b := by
  constructor
  · intro h
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [Fin.val_castSucc, Fin.snoc_castSucc] using h i.castSucc
    · simpa only [Fin.val_last, Fin.snoc_last] using h (Fin.last n)
  · rintro ⟨hs, hb⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.val_last, Fin.snoc_last] using hb
    · simpa only [Fin.val_castSucc, Fin.snoc_castSucc] using hs j

theorem prefixCylinder_split {n : ℕ} (s : Fin n → Bool) :
    prefixCylinder (Fin.snoc s false) ∪ prefixCylinder (Fin.snoc s true) =
      prefixCylinder s := by
  ext x
  simp only [mem_union, mem_prefixCylinder_snoc]
  cases h : x n <;> simp [h]

theorem prefixCylinder_children_disjoint {n : ℕ} (s : Fin n → Bool) :
    Disjoint (prefixCylinder (Fin.snoc s false)) (prefixCylinder (Fin.snoc s true)) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_prefixCylinder_snoc s false x).mp hx
  have hy' := (mem_prefixCylinder_snoc s true x).mp hy
  exact Bool.false_ne_true (hx'.2.symm.trans hy'.2)

def PositiveCylinderProbabilities : Set (ProbabilityMeasure HaarCantor) :=
  {μ | ∀ n : ℕ, ∀ s : Fin n → Bool, 0 < (μ : Measure HaarCantor).real (prefixCylinder s)}

theorem isGδ_positiveCylinderProbabilities : IsGδ PositiveCylinderProbabilities := by
  have hOne (i : HaarNodeIndex) : IsOpen
      {μ : ProbabilityMeasure HaarCantor | 0 < (μ : Measure HaarCantor).real (prefixCylinder i.2)} :=
    isOpen_lt continuous_const (continuous_clopen_mass _ (isClopen_prefixCylinder i.2))
  have heq : PositiveCylinderProbabilities =
      ⋂ i : HaarNodeIndex, {μ : ProbabilityMeasure HaarCantor |
        0 < (μ : Measure HaarCantor).real (prefixCylinder i.2)} := by
    ext μ
    simp only [PositiveCylinderProbabilities, mem_setOf_eq, mem_iInter]
    exact ⟨fun h i => h i.1 i.2, fun h n s => h ⟨n, s⟩⟩
  rw [heq]
  exact IsGδ.iInter_of_isOpen hOne

def cantorHaarNode (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  splitHaar _ (prefixCylinder (Fin.snoc i.2 false)) (prefixCylinder (Fin.snoc i.2 true))
    (isClopen_prefixCylinder _).isClosed.measurableSet
    (isClopen_prefixCylinder _).isClosed.measurableSet

theorem cantorHaarNode_norm (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    ‖cantorHaarNode μ i‖ = 1 :=
  splitHaar_norm _ _ _ _ _ (prefixCylinder_children_disjoint i.2)
    (μ.property (i.1 + 1) (Fin.snoc i.2 false))
    (μ.property (i.1 + 1) (Fin.snoc i.2 true))

theorem cantorHaarNode_inner_one (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    inner ℝ (cantorHaarNode μ i)
      (indicatorConstLp 2 MeasurableSet.univ
        (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) univ) (1 : ℝ)) = 0 :=
  splitHaar_inner_one _ _ _ _ _




end BenchmarkJump
end
end Source1
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarContinuity -/
namespace BenchmarkJumpSubmission
section Source2
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace BenchmarkJump

theorem splitHaar_coe {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (A B : Set α)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    splitHaar μ A B hA hB =ᵐ[μ] fun x =>
      (μ.real B * A.indicator (fun _ => (1 : ℝ)) x -
        μ.real A * B.indicator (fun _ => (1 : ℝ)) x) /
        Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B)) := by
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  let d := Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B))
  filter_upwards [Lp.coeFn_smul d⁻¹ (μ.real B • f - μ.real A • g),
    Lp.coeFn_sub (μ.real B • f) (μ.real A • g), Lp.coeFn_smul (μ.real B) f,
    Lp.coeFn_smul (μ.real A) g,
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := measure_ne_top μ A) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := measure_ne_top μ B) (c := (1 : ℝ))]
    with x hscale hsub hsmulf hsmulg hf hg
  change (d⁻¹ • (μ.real B • f - μ.real A • g)) x = _
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hscale hsub hsmulf hsmulg
  rw [hscale, hsub, hsmulf, hsmulg]
  change f x = A.indicator (fun _ => (1 : ℝ)) x at hf
  change g x = B.indicator (fun _ => (1 : ℝ)) x at hg
  rw [hf, hg]
  change d⁻¹ * (μ.real B * A.indicator (fun _ => (1 : ℝ)) x -
    μ.real A * B.indicator (fun _ => (1 : ℝ)) x) = _
  rw [div_eq_mul_inv, mul_comm]

def cantorHaarFunction (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) (x : HaarCantor) : ℝ :=
  haarNodeFunction (prefixCylinder (Fin.snoc i.2 false))
    (prefixCylinder (Fin.snoc i.2 true)) μ x

theorem cantorHaarNode_coe (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    cantorHaarNode μ i =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      cantorHaarFunction μ i :=
  splitHaar_coe _ _ _ _ _

/-- Each actual Haar basis function has jointly continuous finite-cylinder
coefficients as the full-support measure varies weakly. -/
theorem continuous_cantorHaarFunction (i : HaarNodeIndex) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCantor =>
      cantorHaarFunction p.1 i p.2) := by
  let A := prefixCylinder (Fin.snoc i.2 false)
  let B := prefixCylinder (Fin.snoc i.2 true)
  let map : PositiveCylinderProbabilities → PositiveSplitProbabilities A B :=
    fun μ => ⟨μ, μ.property (i.1 + 1) (Fin.snoc i.2 false),
      μ.property (i.1 + 1) (Fin.snoc i.2 true)⟩
  have hc : Continuous map := continuous_subtype_val.subtype_mk _
  exact (continuous_haarNodeFunction A B (isClopen_prefixCylinder _) (isClopen_prefixCylinder _)).comp
    ((hc.comp continuous_fst).prodMk continuous_snd)




end BenchmarkJump
end
end Source2
end BenchmarkJumpSubmission

/- Preserved source skeleton: HaarMeanZero -/
namespace BenchmarkJumpSubmission
section Source3
open MeasureTheory Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

/-- A Haar difference is orthogonal to every L2 function constant on its
parent cell. The function may be arbitrary outside that cell. -/
theorem splitHaar_inner_eq_zero_of_constant_on_parent
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (g : Lp ℝ 2 μ) (c : ℝ)
    (hg : ∀ᵐ x ∂μ, x ∈ A ∪ B → g x = c) :
    inner ℝ (splitHaar μ A B hA hB) g = 0 := by
  have hIA : inner ℝ (indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)) g =
      μ.real A * c := by
    rw [L2.inner_indicatorConstLp_one]
    have heq : (∫ x in A, g x ∂μ) = ∫ _ in A, c ∂μ :=
      setIntegral_congr_ae hA (hg.mono fun x hx hxA => hx (Or.inl hxA))
    rw [heq, setIntegral_const, smul_eq_mul]
  have hIB : inner ℝ (indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)) g =
      μ.real B * c := by
    rw [L2.inner_indicatorConstLp_one]
    have heq : (∫ x in B, g x ∂μ) = ∫ _ in B, c ∂μ :=
      setIntegral_congr_ae hB (hg.mono fun x hx hxB => hx (Or.inr hxB))
    rw [heq, setIntegral_const, smul_eq_mul]
  unfold splitHaar
  simp only [inner_smul_left, inner_sub_left, RCLike.conj_to_real, hIA, hIB]
  ring



end BenchmarkJump
end
end Source3
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarOrthogonal -/
namespace BenchmarkJumpSubmission
section Source4
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem cantorHaarFunction_eq_of_prefix (μ : PositiveCylinderProbabilities)
    (i : HaarNodeIndex) (x y : HaarCantor)
    (hxy : ∀ j : Fin (i.1 + 1), x j = y j) :
    cantorHaarFunction μ i x = cantorHaarFunction μ i y := by
  classical
  have hC (b : Bool) : x ∈ prefixCylinder (Fin.snoc i.2 b) ↔
      y ∈ prefixCylinder (Fin.snoc i.2 b) := by
    constructor
    · intro hx j
      rw [← hxy j]
      exact hx j
    · intro hy j
      rw [hxy j]
      exact hy j
  unfold cantorHaarFunction haarNodeFunction
  by_cases hxf : x ∈ prefixCylinder (Fin.snoc i.2 false) <;>
    by_cases hxt : x ∈ prefixCylinder (Fin.snoc i.2 true)
  all_goals simp [hxf, hxt, ← hC false, ← hC true]

theorem cantorHaarFunction_constant_of_lt (μ : PositiveCylinderProbabilities)
    {n m : ℕ} (hnm : n < m) (s : Fin n → Bool) (t : Fin m → Bool) :
    ∃ c : ℝ, ∀ x ∈ prefixCylinder t, cantorHaarFunction μ ⟨n, s⟩ x = c := by
  obtain ⟨y, hy⟩ := prefixCylinder_nonempty t
  refine ⟨cantorHaarFunction μ ⟨n, s⟩ y, ?_⟩
  intro x hx
  apply cantorHaarFunction_eq_of_prefix μ ⟨n, s⟩ x y
  intro j
  have hj : (j : ℕ) < n + 1 := j.isLt
  have hjm : (j : ℕ) < m := by omega
  exact (hx ⟨j, hjm⟩).trans (hy ⟨j, hjm⟩).symm

theorem cantorHaarFunction_zero_on_other (μ : PositiveCylinderProbabilities)
    {n : ℕ} (s t : Fin n → Bool) (hst : s ≠ t) :
    ∀ x ∈ prefixCylinder t, cantorHaarFunction μ ⟨n, s⟩ x = 0 := by
  classical
  intro x hx
  have hNot : x ∉ prefixCylinder s := by
    intro hs
    apply hst
    funext j
    exact (hs j).symm.trans (hx j)
  have hf : x ∉ prefixCylinder (Fin.snoc s false) :=
    fun h => hNot ((mem_prefixCylinder_snoc s false x).mp h).1
  have ht : x ∉ prefixCylinder (Fin.snoc s true) :=
    fun h => hNot ((mem_prefixCylinder_snoc s true x).mp h).1
  simp [cantorHaarFunction, haarNodeFunction, hf, ht]

theorem cantorHaarNode_inner_zero_of_constant (μ : PositiveCylinderProbabilities)
    (i j : HaarNodeIndex) (c : ℝ)
    (hConst : ∀ x ∈ prefixCylinder i.2, cantorHaarFunction μ j x = c) :
    inner ℝ (cantorHaarNode μ i) (cantorHaarNode μ j) = 0 := by
  apply splitHaar_inner_eq_zero_of_constant_on_parent _ _ _ _ _ (cantorHaarNode μ j) c
  filter_upwards [cantorHaarNode_coe μ j] with x hx hxParent
  rw [hx]
  apply hConst x
  rw [← prefixCylinder_split]
  exact hxParent

theorem cantorHaarNode_inner_zero_of_lt (μ : PositiveCylinderProbabilities)
    {n m : ℕ} (hnm : n < m) (s : Fin n → Bool) (t : Fin m → Bool) :
    inner ℝ (cantorHaarNode μ ⟨n, s⟩) (cantorHaarNode μ ⟨m, t⟩) = 0 := by
  obtain ⟨c, hc⟩ := cantorHaarFunction_constant_of_lt μ hnm s t
  rw [real_inner_comm]
  exact cantorHaarNode_inner_zero_of_constant μ ⟨m, t⟩ ⟨n, s⟩ c hc

theorem cantorHaarNode_inner_zero_same_level (μ : PositiveCylinderProbabilities)
    {n : ℕ} (s t : Fin n → Bool) (hst : s ≠ t) :
    inner ℝ (cantorHaarNode μ ⟨n, s⟩) (cantorHaarNode μ ⟨n, t⟩) = 0 := by
  rw [real_inner_comm]
  exact cantorHaarNode_inner_zero_of_constant μ ⟨n, t⟩ ⟨n, s⟩ 0
    (cantorHaarFunction_zero_on_other μ s t hst)

/-- All actual normalized binary-tree Haar nodes are orthonormal for every
probability positive on every genuine finite-prefix cylinder. -/
theorem cantorHaarNode_orthonormal (μ : PositiveCylinderProbabilities) :
    Orthonormal ℝ (cantorHaarNode μ) := by
  refine ⟨cantorHaarNode_norm μ, ?_⟩
  rintro ⟨n, s⟩ ⟨m, t⟩ hne
  rcases lt_trichotomy n m with hnm | hnm | hmn
  · exact cantorHaarNode_inner_zero_of_lt μ hnm s t
  · subst m
    apply cantorHaarNode_inner_zero_same_level μ s t
    intro hst
    subst t
    exact hne rfl
  · rw [real_inner_comm]
    exact cantorHaarNode_inner_zero_of_lt μ hmn t s



end BenchmarkJump
end
end Source4
end BenchmarkJumpSubmission

/- Preserved source skeleton: HaarSplitSpan -/
namespace BenchmarkJumpSubmission
section Source5
open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

variable {α : Type*} [MeasurableSpace α]

/-- Each child indicator belongs to the span of the parent indicator and
its actual normalized Haar difference. This is the recursive completeness
step for the varying Cantor Haar basis. -/
theorem splitHaar_children_mem_span (μ : Measure α) [IsFiniteMeasure μ]
    (A B : Set α) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (ha : 0 < μ.real A) (hb : 0 < μ.real B) :
    let parent : Lp ℝ 2 μ :=
      indicatorConstLp 2 (hA.union hB) (measure_ne_top μ _) (1 : ℝ)
    let V := Submodule.span ℝ ({parent, splitHaar μ A B hA hB} : Set (Lp ℝ 2 μ))
    indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ) ∈ V ∧
      indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ) ∈ V := by
  let f : Lp ℝ 2 μ := indicatorConstLp 2 hA (measure_ne_top μ A) (1 : ℝ)
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hB (measure_ne_top μ B) (1 : ℝ)
  let parent : Lp ℝ 2 μ := indicatorConstLp 2 (hA.union hB) (measure_ne_top μ _) (1 : ℝ)
  let w := splitHaar μ A B hA hB
  let V := Submodule.span ℝ ({parent, w} : Set (Lp ℝ 2 μ))
  change f ∈ V ∧ g ∈ V
  have hp : parent ∈ V := Submodule.subset_span (by simp)
  have hw : w ∈ V := Submodule.subset_span (by simp)
  have hparent : parent = f + g := indicatorConstLp_disjoint_union hA hB _ _ hAB 1
  let d : ℝ := Real.sqrt (μ.real A * μ.real B * (μ.real A + μ.real B))
  have hd : d ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsum : μ.real A + μ.real B ≠ 0 := by positivity
  have hwExp : d • w = μ.real B • f - μ.real A • g := by
    change d • (d⁻¹ • (μ.real B • f - μ.real A • g)) = _
    rw [smul_smul, mul_inv_cancel₀ hd, one_smul]
  have hleft : (μ.real A + μ.real B) • f ∈ V := by
    have hlin := V.add_mem (V.smul_mem (μ.real A) hp) (V.smul_mem d hw)
    have heq : μ.real A • parent + d • w = (μ.real A + μ.real B) • f := by
      rw [hparent, hwExp]
      module
    rwa [heq] at hlin
  have hf : f ∈ V := by
    have h := V.smul_mem (μ.real A + μ.real B)⁻¹ hleft
    simpa only [smul_smul, inv_mul_cancel₀ hsum, one_smul] using h
  have hg : g ∈ V := by
    have heq : parent - f = g := by rw [hparent]; abel
    simpa only [heq] using V.sub_mem hp hf
  exact ⟨hf, hg⟩



end BenchmarkJump
end
end Source5
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarSpan -/
namespace BenchmarkJumpSubmission
section Source6
open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def cantorOneVector (μ : PositiveCylinderProbabilities) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℝ)

def cantorPrefixVector (μ : PositiveCylinderProbabilities) {n : ℕ} (s : Fin n → Bool) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  indicatorConstLp 2 (isClopen_prefixCylinder s).isClosed.measurableSet
    (measure_ne_top _ _) (1 : ℝ)

def cantorHaarSpan (μ : PositiveCylinderProbabilities) :
    Submodule ℝ (Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
  Submodule.span ℝ ({cantorOneVector μ} ∪ range (cantorHaarNode μ))

theorem cantorOneVector_mem_span (μ : PositiveCylinderProbabilities) :
    cantorOneVector μ ∈ cantorHaarSpan μ := Submodule.subset_span (Or.inl rfl)

theorem cantorHaarNode_mem_span (μ : PositiveCylinderProbabilities) (i : HaarNodeIndex) :
    cantorHaarNode μ i ∈ cantorHaarSpan μ := Submodule.subset_span (Or.inr ⟨i, rfl⟩)

/-- Every genuine finite-prefix indicator is in the algebraic span of the
constant and the finite-level Haar nodes. -/
theorem cantorPrefixVector_mem_span (μ : PositiveCylinderProbabilities) :
    ∀ n : ℕ, ∀ s : Fin n → Bool, cantorPrefixVector μ s ∈ cantorHaarSpan μ := by
  intro n
  induction n with
  | zero =>
      intro s
      have heq : cantorPrefixVector μ s = cantorOneVector μ := by
        simp only [cantorPrefixVector, prefixCylinder_zero, cantorOneVector]
      rw [heq]
      exact cantorOneVector_mem_span μ
  | succ n ih =>
      intro s
      let t : Fin n → Bool := Fin.init s
      let A := prefixCylinder (Fin.snoc t false)
      let B := prefixCylinder (Fin.snoc t true)
      have hA : MeasurableSet A := (isClopen_prefixCylinder _).isClosed.measurableSet
      have hB : MeasurableSet B := (isClopen_prefixCylinder _).isClosed.measurableSet
      have hParent :
          indicatorConstLp 2 (hA.union hB)
            (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
            (1 : ℝ) ∈ cantorHaarSpan μ := by
        simpa only [A, B, prefixCylinder_split, cantorPrefixVector] using ih t
      have hNode : splitHaar ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          A B hA hB ∈ cantorHaarSpan μ := cantorHaarNode_mem_span μ ⟨n, t⟩
      have hZ : Submodule.span ℝ
          ({indicatorConstLp 2 (hA.union hB)
              (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
              (1 : ℝ), splitHaar ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
                A B hA hB} : Set (Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))) ≤
          cantorHaarSpan μ := by
        apply Submodule.span_le.mpr
        intro v hv
        rcases hv with hv | hv
        · exact hv ▸ hParent
        · exact (mem_singleton_iff.mp hv) ▸ hNode
      have hChildren := splitHaar_children_mem_span
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A B hA hB
        (prefixCylinder_children_disjoint t) (μ.property (n + 1) (Fin.snoc t false))
          (μ.property (n + 1) (Fin.snoc t true))
      have hFalse : cantorPrefixVector μ (Fin.snoc t false) ∈ cantorHaarSpan μ := hZ hChildren.1
      have hTrue : cantorPrefixVector μ (Fin.snoc t true) ∈ cantorHaarSpan μ := hZ hChildren.2
      have hsnoc : Fin.snoc t (s (Fin.last n)) = s := Fin.snoc_init_self s
      cases hlast : s (Fin.last n)
      · rw [hlast] at hsnoc
        simpa only [hsnoc] using hFalse
      · rw [hlast] at hsnoc
        simpa only [hsnoc] using hTrue



end BenchmarkJump
end
end Source6
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarFamily -/
namespace BenchmarkJumpSubmission
section Source7
open MeasureTheory Set
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def cantorHaarFamily (μ : PositiveCylinderProbabilities) :
    Option HaarNodeIndex → Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  | none => cantorOneVector μ
  | some i => cantorHaarNode μ i

theorem cantorOneVector_norm (μ : PositiveCylinderProbabilities) : ‖cantorOneVector μ‖ = 1 := by
  have hinner : inner ℝ (cantorOneVector μ) (cantorOneVector μ) = 1 := by
    simp only [cantorOneVector, L2.real_inner_indicatorConstLp_one_indicatorConstLp_one,
      inter_self]
    simp
  rw [real_inner_self_eq_norm_sq] at hinner
  nlinarith [norm_nonneg (cantorOneVector μ)]

theorem cantorHaarFamily_orthonormal (μ : PositiveCylinderProbabilities) :
    Orthonormal ℝ (cantorHaarFamily μ) := by
  constructor
  · intro i
    cases i with
    | none => exact cantorOneVector_norm μ
    | some i => exact cantorHaarNode_norm μ i
  · intro i j hne
    cases i with
    | none =>
        cases j with
        | none => exact False.elim (hne rfl)
        | some j =>
            rw [real_inner_comm]
            exact cantorHaarNode_inner_one μ j
    | some i =>
        cases j with
        | none => exact cantorHaarNode_inner_one μ i
        | some j =>
            exact (cantorHaarNode_orthonormal μ).inner_eq_zero
              (fun hij => hne (congrArg some hij))

theorem range_cantorHaarFamily (μ : PositiveCylinderProbabilities) :
    range (cantorHaarFamily μ) = {cantorOneVector μ} ∪ range (cantorHaarNode μ) := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    cases i with
    | none => exact Or.inl rfl
    | some i => exact Or.inr ⟨i, rfl⟩
  · rintro (hf | ⟨i, rfl⟩)
    · exact ⟨none, mem_singleton_iff.mp hf |>.symm⟩
    · exact ⟨some i, rfl⟩

theorem span_cantorHaarFamily (μ : PositiveCylinderProbabilities) :
    Submodule.span ℝ (range (cantorHaarFamily μ)) = cantorHaarSpan μ := by
  rw [range_cantorHaarFamily]
  rfl



end BenchmarkJump
end
end Source7
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureUnitaryRN -/
namespace BenchmarkJumpSubmission
section Source8
/-! The genuine complex L² unitary associated to equivalent finite measures.
It multiplies by the square root of the Radon–Nikodym derivative. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

























end MeasureUnitary
end Source8
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureUnitaryMultipliers -/
namespace BenchmarkJumpSubmission
section Source9
/-! Genuine multiplication unitaries in complex L², and their natural
intertwining by the square-root Radon–Nikodym unitary. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (c : α → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)

include hc hnorm















variable (ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]



end MeasureUnitary
end Source9
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureCantorTuple -/
namespace BenchmarkJumpSubmission
section Source10
/-! Countably many genuine L² multiplication unitaries, one for every
clopen finite-coordinate Cantor cylinder. Equivalent measures give
intertwining representations through the actual RN unitary. -/

open MeasureTheory Set

namespace MeasureUnitary

abbrev CantorSpace := ℕ → Bool
abbrev CantorCylinderIndex := Σ s : Finset ℕ, Set (∀ i : s, Bool)

instance : Countable CantorCylinderIndex := inferInstance

def cantorCylinder (k : CantorCylinderIndex) : Set CantorSpace :=
  cylinder k.1 k.2

theorem cantorCylinder_measurable (k : CantorCylinderIndex) : MeasurableSet (cantorCylinder k) := by
  exact (Set.to_countable k.2).measurableSet.cylinder













theorem cantorCylinder_range : Set.range cantorCylinder = measurableCylinders (fun _ : ℕ => Bool) := by
  ext s
  constructor
  · rintro ⟨⟨I, S⟩, rfl⟩
    exact cylinder_mem_measurableCylinders _ _ (Set.to_countable S).measurableSet
  · intro hs
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).mp hs
    exact ⟨⟨I, S⟩, rfl⟩

theorem cantorCylinder_generates :
    MeasurableSpace.generateFrom (Set.range cantorCylinder) = (inferInstance : MeasurableSpace CantorSpace) := by
  rw [cantorCylinder_range, generateFrom_measurableCylinders]

theorem cantorCylinder_isPiSystem : IsPiSystem (Set.range cantorCylinder) := by
  rw [cantorCylinder_range]
  exact isPiSystem_measurableCylinders

end MeasureUnitary
end Source10
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureUnitaryDensity -/
namespace BenchmarkJumpSubmission
section Source11
/-! The spectral-class measure attached to an actual L² vector, expressed
without invoking a spectral theorem. Its mass on a set is the square of the
norm of the corresponding multiplication projection. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

























end MeasureUnitary
end Source11
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureCantorReflection -/
namespace BenchmarkJumpSubmission
section Source12
/-! Reflection of equivalence of finite measures from unitary equivalence
of the countable Cantor-cylinder multiplication representations. -/

open MeasureTheory Set Filter

namespace MeasureUnitary













end MeasureUnitary
end Source12
end BenchmarkJumpSubmission

/- Preserved source skeleton: OperatorFreeGroup -/
namespace BenchmarkJumpSubmission
section Source13
/-!
The free-group step in the representation coding argument.  The topology on
homomorphisms is pointwise convergence, and this file applies to every
topological group, including the strong unitary group of a Hilbert space.
-/

namespace OperatorCoding

variable {ι G : Type*} [Group G]









section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The pointwise topology on group representations. -/
instance representationTopology : TopologicalSpace (FreeGroup ι →* G) :=
  TopologicalSpace.induced (fun ρ : FreeGroup ι →* G => (ρ : FreeGroup ι → G)) inferInstance









end Topological

end OperatorCoding
end Source13
end BenchmarkJumpSubmission

/- Preserved source skeleton: OperatorStrongUnitary -/
namespace BenchmarkJumpSubmission
section Source14
/-!
The strong topology on the actual group of unitary operators.  A unitary is
represented by a surjective complex-linear isometry; the induced topology is
pointwise norm convergence on vectors, not the operator-norm topology.
-/

open Filter Topology

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev StrongUnitary := H ≃ₗᵢ[ℂ] H

instance : TopologicalSpace (StrongUnitary H) :=
  TopologicalSpace.induced (fun u : StrongUnitary H => (u : H → H)) inferInstance

variable {H}

theorem strongUnitary_continuous_eval (x : H) :
    Continuous (fun u : StrongUnitary H => u x) :=
  (continuous_apply x).comp continuous_induced_dom

theorem strongUnitary_continuous_iff {α : Type*} [TopologicalSpace α]
    (f : α → StrongUnitary H) :
    Continuous f ↔ ∀ x, Continuous (fun a => f a x) := by
  constructor
  · intro h x
    exact (strongUnitary_continuous_eval x).comp h
  · intro h
    exact continuous_induced_rng.mpr (continuous_pi h)

theorem strongUnitary_continuous_action {α : Type*} [TopologicalSpace α]
    {u : α → StrongUnitary H} {x : α → H} (hu : Continuous u) (hx : Continuous x) :
    Continuous (fun a => u a (x a)) := by
  rw [continuous_iff_continuousAt]
  intro a
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun b => dist (x b) (x a)) (𝓝 a) (𝓝 0) := by
    simpa using (hx.dist (continuous_const (y := x a))).tendsto a
  have h₂ : Tendsto (fun b => dist (u b (x a)) (u a (x a))) (𝓝 a) (𝓝 0) := by
    simpa using (((strongUnitary_continuous_eval (x a)).comp hu).dist
      (continuous_const (y := u a (x a)))).tendsto a
  apply squeeze_zero (fun b => dist_nonneg) (fun b => ?_) (by simpa using h₁.add h₂)
  calc
    dist (u b (x b)) (u a (x a)) ≤
        dist (u b (x b)) (u b (x a)) + dist (u b (x a)) (u a (x a)) := dist_triangle _ _ _
    _ = dist (x b) (x a) + dist (u b (x a)) (u a (x a)) := by
      congr 1
      exact (u b).toIsometryEquiv.dist_eq _ _

instance strongUnitary_topologicalGroup : IsTopologicalGroup (StrongUnitary H) where
  continuous_mul := by
    apply (strongUnitary_continuous_iff _).mpr
    intro x
    change Continuous (fun p : StrongUnitary H × StrongUnitary H => p.1 (p.2 x))
    exact strongUnitary_continuous_action
      (u := fun p : StrongUnitary H × StrongUnitary H => p.1)
      (x := fun p : StrongUnitary H × StrongUnitary H => p.2 x) continuous_fst
      ((strongUnitary_continuous_eval x).comp continuous_snd)
  continuous_inv := by
    apply (strongUnitary_continuous_iff _).mpr
    intro x
    rw [continuous_iff_continuousAt]
    intro u₀
    apply tendsto_iff_dist_tendsto_zero.mpr
    have h : Tendsto (fun u : StrongUnitary H => dist x (u (u₀⁻¹ x))) (𝓝 u₀) (𝓝 0) := by
      simpa using ((continuous_const (y := x)).dist
        (strongUnitary_continuous_eval (u₀⁻¹ x))).tendsto u₀
    convert h using 1
    funext u
    change dist ((u : H ≃ₗᵢ[ℂ] H).symm x) ((u₀ : H ≃ₗᵢ[ℂ] H).symm x) = _
    rw [← u.toIsometryEquiv.dist_eq]
    simp





end OperatorCoding
end Source14
end BenchmarkJumpSubmission

/- Preserved source skeleton: OperatorNormalization -/
namespace BenchmarkJumpSubmission
section Source15
/-!
The normalization used before coding a bounded operator by two unitaries.
This file proves the normalization is reversible and exactly preserves
unitary equivalence.  It does not claim the spectral/exponential coding step.
-/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

















end OperatorCoding
end Source15
end BenchmarkJumpSubmission

/- Preserved source skeleton: OperatorTargets -/
namespace BenchmarkJumpSubmission
section Source16
/-!
Exact target propositions for Theorems 1.3 and 1.4 of MeasureEquivalence.tex.
These are definitions of the outstanding goals, not proofs of those goals.
The operator topology is strong convergence on vectors. Representations are
all group homomorphisms to the genuine strong unitary group.
-/

open MeasureTheory

namespace OperatorCoding

noncomputable section

abbrev CanonicalHilbert := lp (fun _ : ℕ => ℂ) 2




























end
end OperatorCoding
end Source16
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureCantorAmplified -/
namespace BenchmarkJumpSubmission
section Source17
/-! An infinite-multiplicity Cantor representation, on Hilbert-valued L².
The coefficient Hilbert space is fixed, but the measure-dependent L² spaces
are not yet identified with one canonical Hilbert space in a Borel fashion. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]























end MeasureUnitary
end Source17
end BenchmarkJumpSubmission

/- Preserved source skeleton: HilbertSequenceTopology -/
namespace BenchmarkJumpSubmission
section Source18
/-! The canonical Hilbert space has its actual norm Polish topology;
its coordinate map is a measurable embedding for this topology. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace OperatorCoding

noncomputable section

def hilbertFiniteTruncation (s : Finset ℕ) (x : ℕ → ℂ) : CanonicalHilbert :=
  ∑ i ∈ s, lp.single 2 i (x i)

theorem hilbertFiniteTruncation_continuous (s : Finset ℕ) :
    Continuous (hilbertFiniteTruncation s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℂ) 2 i).continuous.comp
    (continuous_apply i)

instance canonicalHilbert_separable : SeparableSpace CanonicalHilbert := by
  have hd : Dense (⋃ s : Finset ℕ, Set.range (hilbertFiniteTruncation s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
    exact Filter.Eventually.of_forall (fun s => Set.mem_iUnion.mpr ⟨s, ⟨(x:ℕ→ℂ), rfl⟩⟩)
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (hilbertFiniteTruncation_continuous s))

instance canonicalHilbert_polish : PolishSpace CanonicalHilbert := inferInstance

example : SecondCountableTopology CanonicalHilbert := inferInstance





end
end OperatorCoding
end Source18
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureL2Constants -/
namespace BenchmarkJumpSubmission
section Source19
/-! A genuine isometric copy of the coefficient Hilbert space inside
Hilbert-valued L² of a probability measure. This proves that the amplified
Cantor representation has infinite-dimensional fibers, including at atoms. -/

open MeasureTheory Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]











instance cantor_countablyGenerated : MeasurableSpace.CountablyGenerated CantorSpace where
  isCountablyGenerated :=
    ⟨Set.range cantorCylinder, Set.countable_range _, cantorCylinder_generates.symm⟩

instance amplifiedL2_secondCountable (ν : Measure CantorSpace) [SFinite ν] :
    SecondCountableTopology (Lp OperatorCoding.CanonicalHilbert 2 ν) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  infer_instance

end MeasureUnitary
end Source19
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureGramSchmidtBorel -/
namespace BenchmarkJumpSubmission
section Source20
/-! Borel Gram–Schmidt and Borel removal of its zero vectors.
These are fixed-fiber results; a parameter-dependent L² trivialization still
requires a measurable dense fundamental family. -/

open MeasureTheory InnerProductSpace Set Finset

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

























end MeasureUnitary
end Source20
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureCantorDenseFamily -/
namespace BenchmarkJumpSubmission
section Source21
/-! A countable cylinder-indicator fundamental family in the actual
infinite-multiplicity L² fibers. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

theorem cantorCylinder_isSetAlgebra : IsSetAlgebra (Set.range cantorCylinder) where
  empty_mem := ⟨⟨∅, ∅⟩, cylinder_empty ∅⟩
  compl_mem := by
    rintro s ⟨⟨I, S⟩, rfl⟩
    exact ⟨⟨I, Sᶜ⟩, (compl_cylinder (α := fun _ : ℕ => Bool) I S).symm⟩
  union_mem := by
    classical
    rintro s t ⟨⟨I, S⟩, rfl⟩ ⟨⟨J, T⟩, rfl⟩
    exact ⟨⟨I ∪ J, Finset.restrict₂ (π := fun _ : ℕ => Bool) (Finset.subset_union_left (s₁ := I) (s₂ := J)) ⁻¹' S ∪
      Finset.restrict₂ (π := fun _ : ℕ => Bool) (Finset.subset_union_right (s₁ := I) (s₂ := J)) ⁻¹' T⟩,
      (union_cylinder (α := fun _ : ℕ => Bool) I J S T).symm⟩

theorem cantorCylinder_measureDense (μ : Measure CantorSpace) [IsFiniteMeasure μ] :
    μ.MeasureDense (Set.range cantorCylinder) :=
  Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ cantorCylinder_isSetAlgebra
    cantorCylinder_generates.symm

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]



abbrev CantorFundamentalIndex := CantorCylinderIndex × ℕ















instance cantorFundamentalIndex_nonempty : Nonempty CantorFundamentalIndex :=
  ⟨(⟨∅, Set.univ⟩, 0)⟩















end

end MeasureUnitary
end Source21
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarComplete -/
namespace BenchmarkJumpSubmission
section Source22
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

private theorem haar_lp_finset_sum_coe {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (u : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, u i : Lp ℝ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (μ := μ) (E := ℝ) (p := 2))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with x hx hsum
      simpa only [Pi.add_apply, Finset.sum_insert ha] using
        hx.trans (congrArg (fun v => u a x + v) hsum)

def cantorLevelSimple (μ : PositiveCylinderProbabilities) (n : ℕ)
    (u : (Fin n → Bool) → ℝ) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  ∑ s : Fin n → Bool, u s • cantorPrefixVector μ s

theorem cantorLevelSimple_mem_span (μ : PositiveCylinderProbabilities) (n : ℕ)
    (u : (Fin n → Bool) → ℝ) : cantorLevelSimple μ n u ∈ cantorHaarSpan μ :=
  (cantorHaarSpan μ).sum_mem (fun s _ =>
    (cantorHaarSpan μ).smul_mem (u s) (cantorPrefixVector_mem_span μ n s))

theorem cantorLevelSimple_coe (μ : PositiveCylinderProbabilities) (n : ℕ)
    (u : (Fin n → Bool) → ℝ) :
    cantorLevelSimple μ n u =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      fun x => u (fun i : Fin n => x i) := by
  classical
  have hOne (s : Fin n → Bool) :
      (u s • cantorPrefixVector μ s) =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
        fun x => u s * (prefixCylinder s).indicator (fun _ => (1 : ℝ)) x := by
    filter_upwards [Lp.coeFn_smul (u s) (cantorPrefixVector μ s),
      indicatorConstLp_coeFn (p := 2) (hs := (isClopen_prefixCylinder s).isClosed.measurableSet)
        (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
        (c := (1 : ℝ))] with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul] using hx.trans (congrArg (fun z => u s * z) hy)
  have hAll := eventually_countable_forall.mpr hOne
  filter_upwards [haar_lp_finset_sum_coe
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) Finset.univ
      (fun s : Fin n → Bool => u s • cantorPrefixVector μ s), hAll] with x hx hAllx
  change (∑ s : Fin n → Bool, u s • cantorPrefixVector μ s) x = _
  rw [hx]
  simp_rw [hAllx]
  let s₀ : Fin n → Bool := fun i => x i
  rw [Finset.sum_eq_single s₀]
  · simp [prefixCylinder, s₀]
  · intro s _hs hss
    have hNot : x ∉ prefixCylinder s := by
      intro hxs
      apply hss
      funext i
      exact (hxs i).symm
    simp [hNot]
  · simp

/-- Every arbitrary finite-coordinate Cantor cylinder indicator is exactly
a finite-level prefix simple function, hence lies in the Haar span. -/
theorem cantorCylinder_indicator_mem_span (μ : PositiveCylinderProbabilities)
    (k : MeasureUnitary.CantorCylinderIndex) :
    indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ) ∈
        cantorHaarSpan μ := by
  classical
  let N : ℕ := k.1.sup id + 1
  let project : (Fin N → Bool) → (∀ i : k.1, Bool) := fun s i =>
    s ⟨i, Nat.lt_succ_of_le (Finset.le_sup (f := id) i.property)⟩
  let u : (Fin N → Bool) → ℝ := fun s => if project s ∈ k.2 then 1 else 0
  have heq : indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ) =
      cantorLevelSimple μ N u := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2)
      (hs := MeasureUnitary.cantorCylinder_measurable k)
      (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
      (c := (1 : ℝ)), cantorLevelSimple_coe μ N u] with x hx hy
    rw [hx, hy]
    have hp : project (fun i : Fin N => x i) = k.1.restrict x := rfl
    simp only [u, hp, MeasureUnitary.cantorCylinder, mem_cylinder, Set.indicator_apply]
  rw [heq]
  exact cantorLevelSimple_mem_span μ N u

theorem cantorCylinder_constant_mem_span (μ : PositiveCylinderProbabilities)
    (k : MeasureUnitary.CantorCylinderIndex) (c : ℝ) :
    indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) c ∈
        cantorHaarSpan μ := by
  have heq : indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
      (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) c =
      c • indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
        (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2)
      (hs := MeasureUnitary.cantorCylinder_measurable k)
      (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
      (c := c), indicatorConstLp_coeFn (p := 2)
      (hs := MeasureUnitary.cantorCylinder_measurable k)
      (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _)
      (c := (1 : ℝ)), Lp.coeFn_smul c
        (indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k)
          (measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) _) (1 : ℝ))]
      with x hc h1 hs
    simp only [Pi.smul_apply, smul_eq_mul] at hs
    rw [hc, hs, h1]
    by_cases hx : x ∈ MeasureUnitary.cantorCylinder k <;> simp [hx]
  rw [heq]
  exact (cantorHaarSpan μ).smul_mem c (cantorCylinder_indicator_mem_span μ k)

/-- The actual Haar family is complete in the actual real L2 space. -/
theorem cantorHaarSpan_dense (μ : PositiveCylinderProbabilities) :
    (cantorHaarSpan μ).topologicalClosure = ⊤ := by
  let ν : Measure HaarCantor := ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  let V := (cantorHaarSpan μ).topologicalClosure
  have hCylinder (k : MeasureUnitary.CantorCylinderIndex) (c : ℝ) :
      indicatorConstLp 2 (MeasureUnitary.cantorCylinder_measurable k) (measure_ne_top ν _) c ∈ V :=
    (Submodule.le_topologicalClosure (cantorHaarSpan μ)) (cantorCylinder_constant_mem_span μ k c)
  have hAllIndicators (c : ℝ) {s : Set HaarCantor} (hs : MeasurableSet s) (hνs : ν s ≠ ∞) :
      indicatorConstLp 2 hs hνs c ∈ V := by
    letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
    have ha := (MeasureUnitary.cantorCylinder_measureDense ν).indicatorConstLp_subset_closure 2 c
      (show indicatorConstLp 2 hs hνs c ∈
        {indicatorConstLp 2 ht hμt c | (t : Set HaarCantor) (ht : MeasurableSet t) (hμt : ν t ≠ ∞)}
        from ⟨s, hs, hνs, rfl⟩)
    apply closure_minimal (t := (V : Set _)) ?_ (Submodule.isClosed_topologicalClosure _) ha
    rintro x ⟨t, ht, hνt, rfl⟩
    obtain ⟨k, rfl⟩ := ht
    exact hCylinder k c
  have hall : ∀ f : Lp ℝ 2 ν, f ∈ V := by
    apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun f : Lp ℝ 2 ν => f ∈ V)
    · intro c s hs hνs
      exact hAllIndicators c hs hνs.ne
    · intro f g hf hg _hdis hfm hgm
      exact V.add_mem hfm hgm
    · exact Submodule.isClosed_topologicalClosure _
  apply top_unique
  intro f _hf
  exact hall f

def cantorRealHaarBasis (μ : PositiveCylinderProbabilities) :
    HilbertBasis (Option HaarNodeIndex) ℝ
      (Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
  HilbertBasis.mk (cantorHaarFamily_orthonormal μ) (by
    rw [span_cantorHaarFamily, cantorHaarSpan_dense])




end BenchmarkJump
end
end Source22
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorHaarCoordinates -/
namespace BenchmarkJumpSubmission
section Source23
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

abbrev HaarCoefficientSpace := lp (fun _ : Option HaarNodeIndex => ℝ) 2

theorem cantorRealHaarBasis_apply (μ : PositiveCylinderProbabilities) (i : Option HaarNodeIndex) :
    cantorRealHaarBasis μ i = cantorHaarFamily μ i := by
  exact congrFun (HilbertBasis.coe_mk (cantorHaarFamily_orthonormal μ) _) i

def haarLift (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  (cantorRealHaarBasis μ).repr.symm a

theorem norm_haarLift (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    ‖haarLift μ a‖ = ‖a‖ := (cantorRealHaarBasis μ).repr.symm.norm_map a

theorem dist_haarLift (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (haarLift μ a) (haarLift μ b) = dist a b :=
  (cantorRealHaarBasis μ).repr.symm.isometry.dist_eq a b

def haarCoefficientTrunc (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    HaarCoefficientSpace := ∑ i ∈ s, lp.single 2 i (a i)

theorem repr_haar_partial_sum (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    (cantorRealHaarBasis μ).repr (∑ i ∈ s, a i • cantorHaarFamily μ i) =
      haarCoefficientTrunc s a := by
  classical
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, ← cantorRealHaarBasis_apply, HilbertBasis.repr_self]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : Option HaarNodeIndex => ℝ) 2 i (a i) 1).symm



theorem tendsto_haarCoefficientTrunc (a : HaarCoefficientSpace) :
    Tendsto (fun s : Finset (Option HaarNodeIndex) => haarCoefficientTrunc s a) atTop (𝓝 a) :=
  lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) a

def haarFamilyFunction (μ : PositiveCylinderProbabilities)
    (i : Option HaarNodeIndex) (x : HaarCantor) : ℝ :=
  match i with
  | none => 1
  | some i => cantorHaarFunction μ i x

theorem continuous_haarFamilyFunction (i : Option HaarNodeIndex) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCantor =>
      haarFamilyFunction p.1 i p.2) := by
  cases i with
  | none => exact continuous_const
  | some i => exact continuous_cantorHaarFunction i

theorem haarFamilyFunction_coe (μ : PositiveCylinderProbabilities) (i : Option HaarNodeIndex) :
    cantorHaarFamily μ i =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      haarFamilyFunction μ i := by
  cases i with
  | none =>
      simpa only [cantorHaarFamily, cantorOneVector, haarFamilyFunction, indicator_univ] using
        (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
          (hμs := measure_ne_top ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) univ)
          (c := (1 : ℝ)))
  | some i => exact cantorHaarNode_coe μ i

def finiteHaarFunction (s : Finset (Option HaarNodeIndex))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) (x : HaarCantor) : ℝ :=
  ∑ i ∈ s, a i * haarFamilyFunction μ i x

/- Every finite Haar truncation is jointly continuous in weakμ, Hilbert
coefficients and the Cantor point. -/
set_option maxHeartbeats 1500000 in
theorem continuous_finiteHaarFunction (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) × HaarCantor =>
      finiteHaarFunction s p.1.1 p.1.2 p.2) := by
  apply continuous_finsetSum
  intro i _hi
  exact (((lp.lipschitzWith_one_eval 2 i).continuous.comp
    (continuous_snd.comp continuous_fst))).mul
      ((continuous_haarFamilyFunction i).comp
        ((continuous_fst.comp continuous_fst).prodMk continuous_snd))




end BenchmarkJump
end
end Source23
end BenchmarkJumpSubmission

/- Preserved source skeleton: WeakIntegralContinuity -/
namespace BenchmarkJumpSubmission
section Source24
open MeasureTheory Filter Topology

namespace BenchmarkIntegration

variable {K : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]

theorem integral_dist_le_uniform (μ : ProbabilityMeasure K) (f g : C(K, ℝ)) :
    dist (∫ x, f x ∂(μ : Measure K)) (∫ x, g x ∂(μ : Measure K)) ≤ dist f g := by
  have hf : Integrable f (μ : Measure K) :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg : Integrable g (μ : Measure K) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [dist_eq_norm,← integral_sub hf hg,dist_eq_norm]
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure K))
    (f := fun x => f x - g x) (C := ‖f-g‖)
    (Filter.Eventually.of_forall (fun x => (f-g).norm_coe_le_norm x))
  simpa using h

theorem continuous_probability_integral :
    Continuous (fun p : ProbabilityMeasure K × C(K, ℝ) => ∫ x, p.2 x ∂(p.1 : Measure K)) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ : Tendsto (fun q : ProbabilityMeasure K × C(K, ℝ) => dist q.2 p.2) (𝓝 p) (𝓝 0) := by
    simpa using (continuous_snd.dist (continuous_const (y := p.2))).tendsto p
  have hc := (ProbabilityMeasure.continuous_integral_continuousMap p.2).comp
    (continuous_fst : Continuous (fun q : ProbabilityMeasure K × C(K, ℝ) => q.1))
  have h₂ : Tendsto (fun q : ProbabilityMeasure K × C(K, ℝ) =>
      dist (∫ x, p.2 x ∂(q.1 : Measure K)) (∫ x, p.2 x ∂(p.1 : Measure K))) (𝓝 p) (𝓝 0) := by
    simpa using (hc.dist (continuous_const (y := ∫ x, p.2 x ∂(p.1 : Measure K)))).tendsto p
  apply squeeze_zero (fun q => dist_nonneg) (fun q => ?_) (by simpa using h₁.add h₂)
  exact (dist_triangle _ (∫ x, p.2 x ∂(q.1 : Measure K)) _).trans
    (add_le_add (integral_dist_le_uniform q.1 q.2 p.2) le_rfl)

end BenchmarkIntegration
end Source24
end BenchmarkJumpSubmission

/- Preserved source skeleton: HaarLipschitzIntegral -/
namespace BenchmarkJumpSubmission
section Source25
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def haarLipschitzIntegral (φ : ℝ → ℝ) {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (hφ0 : φ 0 = 0) (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) : ℝ :=
  inner ℝ (cantorOneVector μ) (hφ.compLp hφ0 (haarLift μ a))

theorem haarLipschitzIntegral_eq_integral (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0)
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    haarLipschitzIntegral φ hφ hφ0 μ a =
      ∫ x, φ (haarLift μ a x) ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [haarLipschitzIntegral, cantorOneVector, L2.inner_indicatorConstLp_one, setIntegral_univ]
  exact integral_congr_ae (hφ.coeFn_compLp hφ0 (haarLift μ a))

/-- A probability-uniform Lipschitz bound in the fixed coefficient space. -/
theorem haarLipschitzIntegral_dist_le (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0)
    (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (haarLipschitzIntegral φ hφ hφ0 μ a) (haarLipschitzIntegral φ hφ hφ0 μ b) ≤
      (K : ℝ) * dist a b := by
  rw [haarLipschitzIntegral, haarLipschitzIntegral, dist_eq_norm, ← inner_sub_right]
  calc
    _ ≤ ‖hφ.compLp hφ0 (haarLift μ a) - hφ.compLp hφ0 (haarLift μ b)‖ := by
      simpa only [cantorOneVector_norm, one_mul] using norm_inner_le_norm (cantorOneVector μ)
        (hφ.compLp hφ0 (haarLift μ a) - hφ.compLp hφ0 (haarLift μ b))
    _ ≤ (K : ℝ) * ‖haarLift μ a - haarLift μ b‖ :=
      hφ.norm_compLp_sub_le hφ0 (haarLift μ a) (haarLift μ b)
    _ = (K : ℝ) * dist a b := by rw [← dist_eq_norm, dist_haarLift]

theorem continuous_finiteHaar_integral (φ : ℝ → ℝ) (hφ : Continuous φ)
    (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      ∫ x, φ (finiteHaarFunction s p.1 p.2 x)
        ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) := by
  let F : (PositiveCylinderProbabilities × HaarCoefficientSpace) → C(HaarCantor, ℝ) := fun p =>
    ⟨fun x => φ (finiteHaarFunction s p.1 p.2 x),
      (hφ.comp (continuous_finiteHaarFunction s)).comp (continuous_const.prodMk continuous_id)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    (hφ.comp (continuous_finiteHaarFunction s))
  exact BenchmarkIntegration.continuous_probability_integral.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hF)




end BenchmarkJump
end
end Source25
end BenchmarkJumpSubmission

/- Preserved source skeleton: HaarIntegralContinuity -/
namespace BenchmarkJumpSubmission
section Source26
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

private theorem lip_lp_finset_sum_coe {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ι) (u : ι → Lp ℝ 2 μ) :
    (∑ i ∈ s, u i : Lp ℝ 2 μ) =ᵐ[μ] fun x => ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Lp.coeFn_zero (μ := μ) (E := ℝ) (p := 2))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (u a) (∑ i ∈ s, u i), ih] with x hx hsum
      simpa only [Pi.add_apply, Finset.sum_insert ha] using
        hx.trans (congrArg (fun v => u a x + v) hsum)

theorem haarLift_trunc_eq_partial_sum (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    haarLift μ (haarCoefficientTrunc s a) = ∑ i ∈ s, a i • cantorHaarFamily μ i := by
  apply (cantorRealHaarBasis μ).repr.injective
  rw [haarLift, LinearIsometryEquiv.apply_symm_apply, repr_haar_partial_sum]

theorem haarLift_trunc_coe (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    haarLift μ (haarCoefficientTrunc s a) =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      finiteHaarFunction s μ a := by
  rw [haarLift_trunc_eq_partial_sum]
  have hOne (i : Option HaarNodeIndex) :
      (a i • cantorHaarFamily μ i) =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
        fun x => a i * haarFamilyFunction μ i x := by
    filter_upwards [Lp.coeFn_smul (a i) (cantorHaarFamily μ i), haarFamilyFunction_coe μ i]
      with x hx hy
    simpa only [Pi.smul_apply, smul_eq_mul] using hx.trans (congrArg (fun v => a i * v) hy)
  have hAll := eventually_countable_forall.mpr hOne
  filter_upwards [lip_lp_finset_sum_coe
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) s
      (fun i => a i • cantorHaarFamily μ i), hAll] with x hx hAllx
  rw [hx]
  simp_rw [hAllx]
  rfl

theorem haarLipschitzIntegral_trunc_eq (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0) (μ : PositiveCylinderProbabilities)
    (s : Finset (Option HaarNodeIndex)) (a : HaarCoefficientSpace) :
    haarLipschitzIntegral φ hφ hφ0 μ (haarCoefficientTrunc s a) =
      ∫ x, φ (finiteHaarFunction s μ a x)
        ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [haarLipschitzIntegral_eq_integral]
  exact integral_congr_ae ((haarLift_trunc_coe μ s a).fun_comp φ)

theorem continuous_haarLipschitzIntegral_trunc (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0) (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 (haarCoefficientTrunc s p.2)) := by
  have heq : (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 (haarCoefficientTrunc s p.2)) =
      (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
        ∫ x, φ (finiteHaarFunction s p.1 p.2 x)
          ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
    funext fun p => haarLipschitzIntegral_trunc_eq φ hφ hφ0 p.1 s p.2
  rw [heq]
  exact continuous_finiteHaar_integral φ hφ.continuous s

/-- Actual varying-measure Lipschitz integrals are jointly continuous in
the weak probability parameter and normed Haar coefficients. -/
theorem continuous_haarLipschitzIntegral (φ : ℝ → ℝ) {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (hφ0 : φ 0 = 0) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := (K : ℝ) + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hKL : (K : ℝ) ≤ L := by dsimp [L]; linarith
  let δ : ℝ := ε / (8 * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc p₀.2) δ hδ).exists
  let b := haarCoefficientTrunc s p₀.2
  have hb : dist b p₀.2 < δ := hs
  have hFixed : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      haarLipschitzIntegral φ hφ hφ0 p.1 b) :=
    (continuous_haarLipschitzIntegral_trunc φ hφ hφ0 s).comp
      (continuous_fst.prodMk (continuous_const (y := p₀.2)))
  have hNearF := Metric.tendsto_nhds.mp (hFixed.tendsto p₀) (ε / 2) (by positivity)
  have hNearA := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace => p.2)).tendsto p₀)
      δ hδ
  filter_upwards [hNearF, hNearA] with p hpF hpA
  have hTri := dist_triangle
    (haarLipschitzIntegral φ hφ hφ0 p.1 p.2)
    (haarLipschitzIntegral φ hφ hφ0 p.1 b)
    (haarLipschitzIntegral φ hφ hφ0 p₀.1 p₀.2)
  have hTri2 := dist_triangle
    (haarLipschitzIntegral φ hφ hφ0 p.1 b)
    (haarLipschitzIntegral φ hφ hφ0 p₀.1 b)
    (haarLipschitzIntegral φ hφ hφ0 p₀.1 p₀.2)
  have hA := haarLipschitzIntegral_dist_le φ hφ hφ0 p.1 p.2 b
  have hB := haarLipschitzIntegral_dist_le φ hφ hφ0 p₀.1 b p₀.2
  have hAB : dist p.2 b ≤ dist p.2 p₀.2 + dist b p₀.2 := by
    simpa only [dist_comm b p₀.2] using dist_triangle p.2 p₀.2 b
  have hA' : (K : ℝ) * dist p.2 b ≤ L * (dist p.2 p₀.2 + dist b p₀.2) :=
    mul_le_mul hKL hAB dist_nonneg hL.le
  have hB' : (K : ℝ) * dist b p₀.2 ≤ L * dist b p₀.2 :=
    mul_le_mul_of_nonneg_right hKL dist_nonneg
  have hCalc : L * δ = ε / 8 := by
    dsimp [δ]
    field_simp
  nlinarith



end BenchmarkJump
end
end Source26
end BenchmarkJumpSubmission

/- Preserved source skeleton: GdeltaPolish -/
namespace BenchmarkJumpSubmission
section Source27
open Set Topology TopologicalSpace

noncomputable section

namespace BenchmarkJump

/-- Countable intersections of open subsets of a Polish space are Polish
with the inherited topology, via the closed diagonal in a product of open
Polish subspaces. -/
theorem polishSpace_countable_open_intersection
    {X ι : Type*} [TopologicalSpace X] [PolishSpace X] [Countable ι]
    (U : ι → Set X) (hU : ∀ i, IsOpen (U i)) : PolishSpace (⋂ i, U i) := by
  letI : ∀ i, PolishSpace (U i) := fun i => (hU i).polishSpace
  let S : Set X := ⋂ i, U i
  let e : S → X × (∀ i, U i) := fun x =>
    (x, fun i => ⟨x, mem_iInter.mp x.property i⟩)
  have hc : Continuous e := continuous_subtype_val.prodMk
    (continuous_pi fun _ => continuous_subtype_val.subtype_mk _)
  have he : IsEmbedding e :=
    IsEmbedding.of_comp hc continuous_fst (show IsEmbedding (Prod.fst ∘ e) from IsEmbedding.subtypeVal)
  have hRange : range e = {p : X × (∀ i, U i) | ∀ i, (p.2 i : X) = p.1} := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩ i
      rfl
    · intro hp
      have hx : p.1 ∈ S := by
        apply mem_iInter.mpr
        intro i
        exact hp i ▸ (p.2 i).property
      refine ⟨⟨p.1, hx⟩, ?_⟩
      apply Prod.ext
      · rfl
      · funext i
        apply Subtype.ext
        exact (hp i).symm
  have hClosed : IsClosed (range e) := by
    rw [hRange]
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_eq (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd))
      continuous_fst
  exact (show IsClosedEmbedding e from ⟨he, hClosed⟩).polishSpace

theorem polishSpace_of_isGdelta {X : Type*} [TopologicalSpace X] [PolishSpace X]
    {S : Set X} (hS : IsGδ S) : PolishSpace S := by
  obtain ⟨T, hTo, hTc, hEq⟩ := hS
  letI : Countable T := hTc.to_subtype
  have hEq' : S = ⋂ i : T, (i : Set X) := by
    rw [hEq]
    ext x
    simp only [mem_sInter, mem_iInter]
    exact ⟨fun h i => h i i.property, fun h t ht => h ⟨t, ht⟩⟩
  rw [hEq']
  exact polishSpace_countable_open_intersection (fun i : T => (i : Set X))
    (fun i => hTo i i.property)



end BenchmarkJump
end
end Source27
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityTopology -/
namespace BenchmarkJumpSubmission
section Source28
open MeasureTheory Set
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- The actual weak topology on Cantor probability measures is Polish.
Compactness is Prokhorov's theorem; metrizability is the actual weak
Lévy--Prokhorov topology, with no replacement measurable structure. -/
theorem cantorProbability_polish : PolishSpace (ProbabilityMeasure HaarCantor) := by
  letI : MetricSpace (ProbabilityMeasure HaarCantor) :=
    TopologicalSpace.metrizableSpaceMetric (ProbabilityMeasure HaarCantor)
  infer_instance

/-- Positivity on every genuine finite binary-prefix cylinder defines a
Polish subspace with its inherited weak topology. -/
theorem positiveCylinderProbabilities_polish : PolishSpace PositiveCylinderProbabilities := by
  letI : PolishSpace (ProbabilityMeasure HaarCantor) := cantorProbability_polish
  exact polishSpace_of_isGdelta isGδ_positiveCylinderProbabilities




end BenchmarkJump
end
end Source28
end BenchmarkJumpSubmission

/- Preserved source skeleton: PositiveDensityGdelta -/
namespace BenchmarkJumpSubmission
section Source29
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def densityClip (k : ℕ) (t : ℝ) : ℝ := min 1 ((k : ℝ) * max t 0)

theorem lipschitz_densityClip (k : ℕ) : LipschitzWith (k : ℝ≥0) (densityClip k) := by
  have hm : LipschitzWith (k : ℝ≥0) (fun t : ℝ => (k : ℝ) * max t 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := (LipschitzWith.id.max_const (0 : ℝ)).dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h
    calc
      dist ((k : ℝ) * max x 0) ((k : ℝ) * max y 0) =
          (k : ℝ) * dist (max x 0) (max y 0) := by
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity), Real.dist_eq]
      _ ≤ (k : ℝ) * dist x y := mul_le_mul_of_nonneg_left h (by positivity)
      _ = ((k : ℝ≥0) : ℝ) * dist x y := rfl
  exact hm.const_min 1

theorem densityClip_zero (k : ℕ) : densityClip k 0 = 0 := by simp [densityClip]

theorem densityClip_nonneg (k : ℕ) (t : ℝ) : 0 ≤ densityClip k t := by
  unfold densityClip
  positivity

theorem densityClip_le_one (k : ℕ) (t : ℝ) : densityClip k t ≤ 1 := min_le_left _ _

theorem densityClip_tendsto (t : ℝ) :
    Tendsto (fun k : ℕ => densityClip k t) atTop (𝓝 (if 0 < t then (1 : ℝ) else 0)) := by
  by_cases ht : 0 < t
  · simp only [if_pos ht]
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / t)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with k hk
    have hkt : 1 ≤ (k : ℝ) * t := by
      have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
      have hdiv : 1 / t ≤ (k : ℝ) := hN.trans hNk
      exact (div_le_iff₀ ht).mp hdiv
    simp only [densityClip, max_eq_left ht.le, min_eq_left hkt]
  · simp only [if_neg ht]
    have ht0 : t ≤ 0 := le_of_not_gt ht
    simpa only [densityClip, max_eq_right ht0, mul_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
      using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

def positiveIndicator (t : ℝ) : ℝ := if 0 < t then 1 else 0

theorem densityClip_le_positiveIndicator (k : ℕ) (t : ℝ) :
    densityClip k t ≤ positiveIndicator t := by
  by_cases ht : 0 < t
  · simpa only [positiveIndicator, if_pos ht] using densityClip_le_one k t
  · simp [positiveIndicator, ht, densityClip, max_eq_right (le_of_not_gt ht)]

theorem integrable_positiveIndicator {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    Integrable (fun x => positiveIndicator (f x)) μ := by
  have hs : MeasurableSet {x | 0 < f x} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).measurable
  simpa only [positiveIndicator, Set.indicator_apply] using
    (integrable_const (1 : ℝ)).indicator hs

theorem integrable_densityClip {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) (k : ℕ) :
    Integrable (fun x => densityClip k (f x)) μ :=
  MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((lipschitz_densityClip k).comp_memLp (densityClip_zero k) (Lp.memLp f))

theorem tendsto_integral_densityClip {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    Tendsto (fun k : ℕ => ∫ x, densityClip k (f x) ∂μ) atTop
      (𝓝 (∫ x, positiveIndicator (f x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro k
    exact ((lipschitz_densityClip k).continuous.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
  · exact integrable_const 1
  · intro k
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (densityClip_nonneg k (f x))]
      exact densityClip_le_one k (f x)
  · exact Eventually.of_forall fun x => densityClip_tendsto (f x)

/-- Strict positivity almost everywhere is detected by a countable family
of strict integral inequalities; no nonnegative-cone assumption is needed. -/
theorem ae_positive_iff_densityClip {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : Lp ℝ 2 μ) :
    (∀ᵐ x ∂μ, 0 < f x) ↔
      ∀ r : ℕ, ∃ k : ℕ,
        1 - 1 / (r + 1 : ℝ) < ∫ x, densityClip k (f x) ∂μ := by
  classical
  let I : ℝ := ∫ x, positiveIndicator (f x) ∂μ
  have hI : I ≤ 1 := by
    have h := integral_mono (integrable_positiveIndicator μ f) (integrable_const (1 : ℝ))
      (fun x => by unfold positiveIndicator; split_ifs <;> norm_num)
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using h
  constructor
  · intro hPos r
    have hIone : I = 1 := by
      have hae : (fun x => positiveIndicator (f x)) =ᵐ[μ] fun _ => (1 : ℝ) :=
        hPos.mono fun x hx => by simp only [positiveIndicator, if_pos hx]
      simpa only [I, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
        integral_congr_ae hae
    have hLim : Tendsto (fun k : ℕ => ∫ x, densityClip k (f x) ∂μ) atTop (𝓝 (1 : ℝ)) := by
      simpa only [← hIone] using tendsto_integral_densityClip μ f
    have hlt : 1 - 1 / (r + 1 : ℝ) < 1 := by
      have hpos : 0 < 1 / (r + 1 : ℝ) := by positivity
      linarith
    exact ((tendsto_order.mp hLim).1 _ hlt).exists
  · intro hTests
    have hIone : I = 1 := by
      apply le_antisymm hI
      by_contra! hIlow
      obtain ⟨r, hr⟩ := exists_nat_one_div_lt (sub_pos.mpr hIlow)
      obtain ⟨k, hk⟩ := hTests r
      have hClip : (∫ x, densityClip k (f x) ∂μ) ≤ I :=
        integral_mono (integrable_densityClip μ f k) (integrable_positiveIndicator μ f)
          (fun x => densityClip_le_positiveIndicator k (f x))
      linarith
    have hnon : ∀ x, 0 ≤ 1 - positiveIndicator (f x) := by
      intro x
      unfold positiveIndicator
      split_ifs <;> norm_num
    have hIntZero : (∫ x, 1 - positiveIndicator (f x) ∂μ) = 0 := by
      rw [integral_sub (integrable_const 1) (integrable_positiveIndicator μ f)]
      simpa only [I, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using
        sub_eq_zero.mpr hIone.symm
    have hAe := (integral_eq_zero_iff_of_nonneg hnon
      ((integrable_const 1).sub (integrable_positiveIndicator μ f))).mp hIntZero
    filter_upwards [hAe] with x hx
    by_contra hnot
    simp only [positiveIndicator, if_neg hnot] at hx
    norm_num at hx

def StrictPositiveHaarParameters : Set (PositiveCylinderProbabilities × HaarCoefficientSpace) :=
  {p | ∀ᵐ x ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor), 0 < haarLift p.1 p.2 x}

theorem isGδ_strictPositiveHaarParameters : IsGδ StrictPositiveHaarParameters := by
  have heq : StrictPositiveHaarParameters = ⋂ r : ℕ, ⋃ k : ℕ,
      {p : PositiveCylinderProbabilities × HaarCoefficientSpace |
        1 - 1 / (r + 1 : ℝ) <
          haarLipschitzIntegral (densityClip k) (lipschitz_densityClip k) (densityClip_zero k) p.1 p.2} := by
    ext p
    simp only [StrictPositiveHaarParameters, mem_setOf_eq, mem_iInter, mem_iUnion,
      ae_positive_iff_densityClip, haarLipschitzIntegral_eq_integral]
  rw [heq]
  apply IsGδ.iInter_of_isOpen
  intro r
  apply isOpen_iUnion
  intro k
  exact isOpen_lt continuous_const
    (continuous_haarLipschitzIntegral (densityClip k) (lipschitz_densityClip k) (densityClip_zero k))




end BenchmarkJump
end
end Source29
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensitySquare -/
namespace BenchmarkJumpSubmission
section Source30
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











end MeasureEquivalenceDensity
end Source30
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityMeasure -/
namespace BenchmarkJumpSubmission
section Source31
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



end MeasureEquivalenceDensity
end Source31
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityBundleTopology -/
namespace BenchmarkJumpSubmission
section Source32
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def haarTruncateFromProduct (s : Finset (Option HaarNodeIndex))
    (x : Option HaarNodeIndex → ℝ) : HaarCoefficientSpace :=
  ∑ i ∈ s, lp.single 2 i (x i)

theorem continuous_haarTruncateFromProduct (s : Finset (Option HaarNodeIndex)) :
    Continuous (haarTruncateFromProduct s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : Option HaarNodeIndex => ℝ) 2 i).continuous.comp
    (continuous_apply i)

theorem haarCoefficientSpace_separable : SeparableSpace HaarCoefficientSpace := by
  have hd : Dense (⋃ s : Finset (Option HaarNodeIndex), range (haarTruncateFromProduct s)) := by
    intro a
    apply mem_closure_of_tendsto (tendsto_haarCoefficientTrunc a)
    exact Eventually.of_forall fun s => mem_iUnion.mpr ⟨s, ⟨(a : Option HaarNodeIndex → ℝ), rfl⟩⟩
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion fun s => isSeparable_range (continuous_haarTruncateFromProduct s)

theorem haarCoefficientSpace_polish : PolishSpace HaarCoefficientSpace := by
  letI : SeparableSpace HaarCoefficientSpace := haarCoefficientSpace_separable
  infer_instance

def PositiveDensityParameters : Set (PositiveCylinderProbabilities × HaarCoefficientSpace) :=
  StrictPositiveHaarParameters ∩ {p | ‖p.2‖ = 1}

theorem isGδ_positiveDensityParameters : IsGδ PositiveDensityParameters := by
  letI : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
  letI : PolishSpace HaarCoefficientSpace := haarCoefficientSpace_polish
  exact isGδ_strictPositiveHaarParameters.inter
    ((isClosed_eq continuous_snd.norm continuous_const).isGδ)

abbrev PositiveDensityBundle := PositiveDensityParameters

/-- The actual norm-one strictly-positive square-density bundle is Polish. -/
theorem positiveDensityBundle_polish : PolishSpace PositiveDensityBundle := by
  letI : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
  letI : PolishSpace HaarCoefficientSpace := haarCoefficientSpace_polish
  exact polishSpace_of_isGdelta isGδ_positiveDensityParameters

def densitySource (z : PositiveDensityBundle) : PositiveCylinderProbabilities := z.1.1

def densityVector (z : PositiveDensityBundle) :
    Lp ℝ 2 ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  haarLift z.1.1 z.1.2

theorem densityVector_positive (z : PositiveDensityBundle) :
    ∀ᵐ x ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < densityVector z x := z.property.1

theorem densityVector_norm (z : PositiveDensityBundle) : ‖densityVector z‖ = 1 := by
  exact (norm_haarLift z.1.1 z.1.2).trans z.property.2

theorem continuous_densitySource : Continuous densitySource :=
  continuous_fst.comp continuous_subtype_val

theorem integral_densityVector_sq (z : PositiveDensityBundle) :
    (∫ x, densityVector z x ^ 2
      ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) = 1 := by
  calc
    _ = inner ℝ (densityVector z) (densityVector z) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by simp [pow_two]
    _ = ‖densityVector z‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = 1 := by rw [densityVector_norm]; norm_num

def densityTargetMeasure (z : PositiveDensityBundle) : Measure HaarCantor :=
  ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
    (fun x => ENNReal.ofReal (densityVector z x ^ 2))

theorem densityTargetMeasure_univ (z : PositiveDensityBundle) : densityTargetMeasure z univ = 1 := by
  unfold densityTargetMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (MeasureEquivalenceDensity.integrable_square _ (densityVector z))
      (Eventually.of_forall fun x => sq_nonneg (densityVector z x)),
    integral_densityVector_sq, ENNReal.ofReal_one]

def densityTargetProbability (z : PositiveDensityBundle) : ProbabilityMeasure HaarCantor :=
  ⟨densityTargetMeasure z, ⟨densityTargetMeasure_univ z⟩⟩

instance densityTargetMeasure_isProbability (z : PositiveDensityBundle) :
    IsProbabilityMeasure (densityTargetMeasure z) := ⟨densityTargetMeasure_univ z⟩

theorem densityTarget_ac_source (z : PositiveDensityBundle) :
    densityTargetMeasure z ≪ ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  withDensity_absolutelyContinuous _ _

theorem densitySource_ac_target (z : PositiveDensityBundle) :
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ densityTargetMeasure z := by
  apply withDensity_absolutelyContinuous'
  · exact (((Lp.aestronglyMeasurable (densityVector z)).aemeasurable.pow_const 2).ennreal_ofReal)
  · filter_upwards [densityVector_positive z] with x hx
    exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hx)).ne'

/-- Squaring the genuine positive unit density yields another full-support
Cantor probability, mutually absolutely continuous with its source. -/
def densityTarget (z : PositiveDensityBundle) : PositiveCylinderProbabilities :=
  ⟨densityTargetProbability z, by
    intro n s
    apply ENNReal.toReal_pos
    · intro hzero
      have hz := densitySource_ac_target z hzero
      have hpos := (densitySource z).property n s
      change 0 < (((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        (prefixCylinder s)).toReal at hpos
      rw [hz, ENNReal.toReal_zero] at hpos
      exact lt_irrefl _ hpos
    · exact measure_ne_top (densityTargetMeasure z) _⟩

theorem densitySource_target_equivalent (z : PositiveDensityBundle) :
    (((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) ∧
    (((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :=
  ⟨densitySource_ac_target z, densityTarget_ac_source z⟩




end BenchmarkJump
end
end Source32
end BenchmarkJumpSubmission

/- Preserved source skeleton: HellingerTransport -/
namespace BenchmarkJumpSubmission
section Source33
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



end MeasureEquivalenceHellinger
end Source33
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityGraphCompleteness -/
namespace BenchmarkJumpSubmission
section Source34
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







end MeasureEquivalenceDensityGraph

namespace MeasureEquivalenceInverseAC

open MeasureTheory





end MeasureEquivalenceInverseAC
end Source34
end BenchmarkJumpSubmission

/- Preserved source skeleton: PolishGroupTopology -/
namespace BenchmarkJumpSubmission
section Source35
/-!
Pettis category, Borel-homomorphism continuity, and uniqueness of compatible
Polish group topologies. This is a new standalone verification development.
-/

open Filter Set TopologicalSpace
open scoped Topology Pointwise

namespace MeasureEquivalenceTopology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [BaireSpace G]





section Polish

variable [PolishSpace G] [MeasurableSpace G] [BorelSpace G]
  {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [PolishSpace L] [MeasurableSpace L] [BorelSpace L]





end Polish

end MeasureEquivalenceTopology
end Source35
end BenchmarkJumpSubmission

/- Preserved source skeleton: RNGraph -/
namespace BenchmarkJumpSubmission
section Source36
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

















end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]









end Graph

end MeasureEquivalenceRNGraph
end Source36
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityInversion -/
namespace BenchmarkJumpSubmission
section Source37
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def inverseDensityVector (z : PositiveDensityBundle) :
    Lp ℝ 2 ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  MeasureEquivalenceHellinger.root
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)

theorem inverseDensityVector_norm (z : PositiveDensityBundle) : ‖inverseDensityVector z‖ = 1 :=
  MeasureEquivalenceHellinger.root_probability_norm _ _ (densitySource_ac_target z)

theorem inverseDensityVector_positive (z : PositiveDensityBundle) :
    ∀ᵐ x ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < inverseDensityVector z x := by
  letI : SigmaFinite (densityTargetMeasure z) := inferInstance
  filter_upwards [MeasureEquivalenceHellinger.root_coe
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
    (densityTarget_ac_source z).ae_le (Measure.rnDeriv_pos (densitySource_ac_target z)),
    Measure.rnDeriv_ne_top
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)] with x hx hp ht
  rw [show inverseDensityVector z x = _ from hx]
  exact Real.sqrt_pos.mpr (ENNReal.toReal_pos hp.ne' ht)

def densityInverseCoefficients (z : PositiveDensityBundle) : HaarCoefficientSpace :=
  (cantorRealHaarBasis (densityTarget z)).repr (inverseDensityVector z)

def densityInverse (z : PositiveDensityBundle) : PositiveDensityBundle :=
  ⟨(densityTarget z, densityInverseCoefficients z), by
    constructor
    · change ∀ᵐ x ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
        0 < haarLift (densityTarget z) (densityInverseCoefficients z) x
      rw [haarLift, densityInverseCoefficients, LinearIsometryEquiv.symm_apply_apply]
      exact inverseDensityVector_positive z
    · change ‖(cantorRealHaarBasis (densityTarget z)).repr (inverseDensityVector z)‖ = 1
      rw [LinearIsometryEquiv.norm_map, inverseDensityVector_norm]⟩

@[simp] theorem densitySource_inverse (z : PositiveDensityBundle) :
    densitySource (densityInverse z) = densityTarget z := rfl

@[simp] theorem densityVector_inverse (z : PositiveDensityBundle) :
    densityVector (densityInverse z) = inverseDensityVector z :=
  (cantorRealHaarBasis (densityTarget z)).repr.symm_apply_apply _

theorem densityTargetMeasure_inverse (z : PositiveDensityBundle) :
    densityTargetMeasure (densityInverse z) =
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  change (MeasureEquivalenceDensity.squareMeasure
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (densityVector (densityInverse z)) : Measure HaarCantor) = _
  rw [densityVector_inverse]
  exact MeasureEquivalenceRNGraph.squareMeasure_root _ _ (densitySource_ac_target z)

@[simp] theorem densityTarget_inverse (z : PositiveDensityBundle) :
    densityTarget (densityInverse z) = densitySource z := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  exact densityTargetMeasure_inverse z

theorem densityBundle_endpoint_ext {z w : PositiveDensityBundle}
    (hs : densitySource z = densitySource w)
    (ht : densityTargetMeasure z = densityTargetMeasure w) : z = w := by
  rcases z with ⟨⟨μ, a⟩, hz⟩
  rcases w with ⟨⟨ν, b⟩, hw⟩
  change μ = ν at hs
  subst ν
  have haAE : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < haarLift μ a x := hz.1
  have hbAE : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < haarLift μ b x := hw.1
  have haPos : 0 ≤ haarLift μ a := (Lp.coeFn_nonneg _).mp (haAE.mono fun _ hx => hx.le)
  have hbPos : 0 ≤ haarLift μ b := (Lp.coeFn_nonneg _).mp (hbAE.mono fun _ hx => hx.le)
  have hsq : MeasureEquivalenceDensity.squareMeasure
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ a) =
      MeasureEquivalenceDensity.squareMeasure
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ b) := by
    apply Subtype.ext
    exact ht
  have hvec := MeasureEquivalenceDensity.squareMeasure_injective_nonnegative
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) haPos hbPos hsq
  have hab : a = b := (cantorRealHaarBasis μ).repr.symm.injective hvec
  subst b
  rfl

theorem densityInverse_involutive : Function.Involutive densityInverse := by
  intro z
  apply densityBundle_endpoint_ext
  · simp
  · rw [densityTargetMeasure_inverse]
    rfl




end BenchmarkJump
end
end Source37
end BenchmarkJumpSubmission

/- Preserved source skeleton: HellingerAffinity -/
namespace BenchmarkJumpSubmission
section Source38
/-!
Actual Hellinger affinity of finite measures via their L2 square-root RN
densities against their sum. This file proves the probability bounds and
the equivalence between zero affinity and mutual singularity.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureEquivalenceHellinger

variable {Y : Type*} [MeasurableSpace Y]





















end MeasureEquivalenceHellinger
end Source38
end BenchmarkJumpSubmission

/- Preserved source skeleton: WeightedRootSwitch -/
namespace BenchmarkJumpSubmission
section Source39
open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace BenchmarkJump

variable {Y : Type*} [MeasurableSpace Y]

def weightedAffinityAgainst (g : Y → ℝ) (μ ν ρ : Measure Y) : ℝ :=
  ∫ x, g x * (Real.sqrt (μ.rnDeriv ρ x).toReal *
    Real.sqrt (ν.rnDeriv ρ x).toReal) ∂ρ

theorem weightedAffinityAgainst_change_reference (g : Y → ℝ) (μ ν ρ σ : Measure Y)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite σ]
    (hμ : μ ≪ ρ) (hν : ν ≪ ρ) (hρ : ρ ≪ σ) :
    weightedAffinityAgainst g μ ν σ = weightedAffinityAgainst g μ ν ρ := by
  unfold weightedAffinityAgainst
  rw [← integral_toReal_rnDeriv_mul hρ]
  apply integral_congr_ae
  filter_upwards [Measure.rnDeriv_mul_rnDeriv (κ := σ) hμ,
    Measure.rnDeriv_mul_rnDeriv (κ := σ) hν] with x hmx hnx
  simp only [Pi.mul_apply] at hmx hnx
  rw [← hmx, ← hnx, ENNReal.toReal_mul, ENNReal.toReal_mul,
    Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_mul ENNReal.toReal_nonneg]
  calc
    _ = g x * (Real.sqrt (ρ.rnDeriv σ x).toReal) ^ 2 *
        (Real.sqrt (μ.rnDeriv ρ x).toReal * Real.sqrt (ν.rnDeriv ρ x).toReal) := by ring
    _ = _ := by rw [Real.sq_sqrt ENNReal.toReal_nonneg]; ring

/-- Change of orientation of a weighted square-root density integral.
This is an actual RN change-of-measure identity. -/
theorem weighted_root_switch (g : Y → ℝ) (μ ν : Measure Y)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    (∫ x, g x * MeasureEquivalenceHellinger.root μ ν x ∂ν) =
      ∫ x, g x * MeasureEquivalenceHellinger.root ν μ x ∂μ := by
  have hν : weightedAffinityAgainst g μ ν ν =
      ∫ x, g x * MeasureEquivalenceHellinger.root μ ν x ∂ν := by
    unfold weightedAffinityAgainst
    apply integral_congr_ae
    filter_upwards [Measure.rnDeriv_self ν,
      MeasureEquivalenceHellinger.root_coe μ ν] with x hself hr
    rw [hself, ENNReal.toReal_one, Real.sqrt_one, mul_one, hr]
  have hμ : weightedAffinityAgainst g μ ν μ =
      ∫ x, g x * MeasureEquivalenceHellinger.root ν μ x ∂μ := by
    unfold weightedAffinityAgainst
    apply integral_congr_ae
    filter_upwards [Measure.rnDeriv_self μ,
      MeasureEquivalenceHellinger.root_coe ν μ] with x hself hr
    rw [hself, ENNReal.toReal_one, Real.sqrt_one, one_mul, hr]
  rw [← hν, ← hμ]
  exact (weightedAffinityAgainst_change_reference g μ ν ν μ hμν
    Measure.AbsolutelyContinuous.rfl hνμ).symm



end BenchmarkJump
end
end Source39
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityInverseIntegral -/
namespace BenchmarkJumpSubmission
section Source40
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem root_densityTarget_eq (z : PositiveDensityBundle) :
    MeasureEquivalenceHellinger.root
      ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) = densityVector z := by
  have hPos : 0 ≤ densityVector z :=
    (Lp.coeFn_nonneg _).mp ((densityVector_positive z).mono fun _ hx => hx.le)
  apply MeasureEquivalenceDensity.squareMeasure_injective_nonnegative
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (MeasureEquivalenceHellinger.root_nonnegative _ _) hPos
  apply Subtype.ext
  exact MeasureEquivalenceRNGraph.squareMeasure_root
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (by exact densityTarget_ac_source z)

/-- Actual inversion formula for every real test function; no continuity or
integrability of the test is required for this identity. -/
theorem integral_inverseDensityVector (z : PositiveDensityBundle) (g : HaarCantor → ℝ) :
    (∫ x, g x * inverseDensityVector z x
      ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) =
      ∫ x, g x * densityVector z x
        ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  have hSwitch := weighted_root_switch g
    ((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (densitySource_ac_target z) (densityTarget_ac_source z)
  rw [root_densityTarget_eq] at hSwitch
  exact hSwitch



end BenchmarkJump
end
end Source40
end BenchmarkJumpSubmission

/- Preserved source skeleton: SquareTestEstimate -/
namespace BenchmarkJumpSubmission
section Source41
open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace BenchmarkIntegration

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K]

theorem square_test_difference_bound (μ : Measure K) (f g : Lp ℝ 2 μ) (h : C(K, ℝ)) :
    |(∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ f : Measure K)) -
      (∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ g : Measure K))| ≤
      ‖h‖ * ‖f - g‖ * (‖f‖ + ‖g‖) := by
  let k := MeasureEquivalenceDensity.square μ f - MeasureEquivalenceDensity.square μ g
  have hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ ‖h‖ := Eventually.of_forall h.norm_coe_le_norm
  have hf := (MeasureEquivalenceDensity.integrable_square μ f).mul_bdd
    h.continuous.aestronglyMeasurable hb
  have hg := (MeasureEquivalenceDensity.integrable_square μ g).mul_bdd
    h.continuous.aestronglyMeasurable hb
  have hk : k =ᵐ[μ] (fun x => f x ^ 2 - g x ^ 2) := by
    filter_upwards [Lp.coeFn_sub (MeasureEquivalenceDensity.square μ f)
      (MeasureEquivalenceDensity.square μ g),
      MeasureEquivalenceDensity.square_coe μ f,
      MeasureEquivalenceDensity.square_coe μ g] with x hs h1 h2
    change k x = _
    simp only [Pi.sub_apply] at hs
    rw [show k x = _ from hs, h1, h2]
  have he : (∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ f : Measure K)) -
      (∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure μ g : Measure K)) =
      ∫ x, h x * k x ∂μ := by
    rw [MeasureEquivalenceDensity.squareMeasure_integral,
      MeasureEquivalenceDensity.squareMeasure_integral, ← integral_sub hf hg]
    apply integral_congr_ae
    filter_upwards [hk] with x hx
    rw [hx]
    ring
  rw [he, ← Real.norm_eq_abs]
  have hi := norm_integral_le_of_norm_le (f := fun x : K => h x * k x)
    ((L1.integrable_coeFn k).norm.const_mul ‖h‖)
    (Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm x) (norm_nonneg (k x))))
  have hi' : ‖∫ x, h x * k x ∂μ‖ ≤ ‖h‖ * ‖k‖ := by
    simpa only [integral_const_mul, ← L1.norm_eq_integral_norm] using hi
  calc
    _ ≤ ‖h‖ * ‖k‖ := hi'
    _ ≤ ‖h‖ * (‖f - g‖ * (‖f‖ + ‖g‖)) :=
      mul_le_mul_of_nonneg_left (MeasureEquivalenceDensity.square_difference_bound μ f g) (norm_nonneg _)
    _ = _ := by ring

end BenchmarkIntegration
end
end Source41
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityTargetContinuity -/
namespace BenchmarkJumpSubmission
section Source42
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def squareHaarIntegral (h : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) : ℝ :=
  ∫ x, h x ∂(MeasureEquivalenceDensity.squareMeasure
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ a) : Measure HaarCantor)

theorem squareHaarIntegral_dist_le (h : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (squareHaarIntegral h μ a) (squareHaarIntegral h μ b) ≤
      ‖h‖ * dist a b * (‖a‖ + ‖b‖) := by
  have hBound := BenchmarkIntegration.square_test_difference_bound
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (haarLift μ a) (haarLift μ b) h
  simpa only [squareHaarIntegral, Real.dist_eq, ← dist_eq_norm,
    dist_haarLift, norm_haarLift] using hBound

theorem squareHaarIntegral_trunc_eq (h : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (s : Finset (Option HaarNodeIndex))
    (a : HaarCoefficientSpace) :
    squareHaarIntegral h μ (haarCoefficientTrunc s a) =
      ∫ x, h x * (finiteHaarFunction s μ a x) ^ 2
        ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [squareHaarIntegral, MeasureEquivalenceDensity.squareMeasure_integral]
  apply integral_congr_ae
  filter_upwards [haarLift_trunc_coe μ s a] with x hx
  rw [hx, mul_comm]

theorem continuous_squareHaarIntegral_trunc (h : C(HaarCantor, ℝ))
    (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      squareHaarIntegral h p.1 (haarCoefficientTrunc s p.2)) := by
  let F : (PositiveCylinderProbabilities × HaarCoefficientSpace) → C(HaarCantor, ℝ) := fun p =>
    ⟨fun x => h x * (finiteHaarFunction s p.1 p.2 x) ^ 2,
      h.continuous.mul (((continuous_finiteHaarFunction s).comp
        (continuous_const.prodMk continuous_id)).pow 2)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    ((h.continuous.comp continuous_snd).mul ((continuous_finiteHaarFunction s).pow 2))
  have hc := BenchmarkIntegration.continuous_probability_integral.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hF)
  change Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
    ∫ x, h x * (finiteHaarFunction s p.1 p.2 x) ^ 2
      ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) at hc
  simpa only [squareHaarIntegral_trunc_eq] using hc

/- Weak integrals of the actual square density vary continuously with both
the source probability and the common Hilbert coefficients. -/
set_option maxHeartbeats 500000 in
theorem continuous_squareHaarIntegral (h : C(HaarCantor, ℝ)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      squareHaarIntegral h p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := (‖h‖ + 1) * (2 * ‖p₀.2‖ + 3)
  have hC : 0 < C := by dsimp [C]; positivity
  let δ : ℝ := min 1 (ε / (8 * C))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδe : C * δ ≤ ε / 8 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (ε / (8 * C))) hC.le
    have he : C * (ε / (8 * C)) = ε / 8 := by field_simp
    exact hh.trans_eq he
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc p₀.2) δ hδ).exists
  let b := haarCoefficientTrunc s p₀.2
  have hb : dist b p₀.2 < δ := hs
  have hbN : ‖b‖ ≤ ‖p₀.2‖ + 1 := by
    have hn : ‖b‖ ≤ dist b p₀.2 + ‖p₀.2‖ := by
      simpa only [dist_zero_right] using dist_triangle b p₀.2 0
    linarith only [hn, hb, hδ1]
  have hFixed : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      squareHaarIntegral h p.1 b) := by
    have hPair : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
        (p.1, p₀.2)) := continuous_fst.prodMk continuous_const
    have hc := (continuous_squareHaarIntegral_trunc h s).comp hPair
    exact hc
  have hNearF := Metric.tendsto_nhds.mp (hFixed.tendsto p₀) (ε / 2) (by positivity)
  have hNearA := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace => p.2)).tendsto p₀)
      δ hδ
  filter_upwards [hNearF, hNearA] with p hpF hpA
  change dist (squareHaarIntegral h p.1 b) (squareHaarIntegral h p₀.1 b) < ε / 2 at hpF
  have hpN : ‖p.2‖ ≤ ‖p₀.2‖ + 1 := by
    have hn : ‖p.2‖ ≤ dist p.2 p₀.2 + ‖p₀.2‖ := by
      simpa only [dist_zero_right] using dist_triangle p.2 p₀.2 0
    linarith only [hn, hpA, hδ1]
  have hLocal (u v : HaarCoefficientSpace) (hu : ‖u‖ ≤ ‖p₀.2‖ + 1)
      (hv : ‖v‖ ≤ ‖p₀.2‖ + 1) (μ : PositiveCylinderProbabilities) :
      dist (squareHaarIntegral h μ u) (squareHaarIntegral h μ v) ≤ C * dist u v := by
    have hsN : ‖u‖ + ‖v‖ ≤ 2 * ‖p₀.2‖ + 3 := by linarith only [hu, hv]
    have hh : ‖h‖ * (‖u‖ + ‖v‖) ≤ C := by
      dsimp [C]
      exact mul_le_mul (by linarith only [norm_nonneg h]) hsN (by positivity) (by positivity)
    calc
      _ ≤ ‖h‖ * dist u v * (‖u‖ + ‖v‖) := squareHaarIntegral_dist_le h μ u v
      _ = (‖h‖ * (‖u‖ + ‖v‖)) * dist u v := by ring
      _ ≤ C * dist u v := mul_le_mul_of_nonneg_right hh dist_nonneg
  have hA := hLocal p.2 b hpN hbN p.1
  have hB := hLocal b p₀.2 hbN (by linarith only) p₀.1
  have hTri := dist_triangle (squareHaarIntegral h p.1 p.2)
    (squareHaarIntegral h p.1 b) (squareHaarIntegral h p₀.1 p₀.2)
  have hTri2 := dist_triangle (squareHaarIntegral h p.1 b)
    (squareHaarIntegral h p₀.1 b) (squareHaarIntegral h p₀.1 p₀.2)
  have hAB : dist p.2 b ≤ dist p.2 p₀.2 + dist b p₀.2 := by
    simpa only [dist_comm b p₀.2] using dist_triangle p.2 p₀.2 b
  have hMul := mul_le_mul_of_nonneg_left hAB hC.le
  rw [mul_add] at hMul
  have hSmallA := mul_lt_mul_of_pos_left hpA hC
  have hSmallB := mul_lt_mul_of_pos_left hb hC
  linarith only [hTri, hTri2, hA, hB, hMul, hSmallA, hSmallB, hδe, hpF, hε]

theorem continuous_densityTargetProbability : Continuous densityTargetProbability := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro h
  change Continuous (fun z : PositiveDensityBundle => squareHaarIntegral h z.1.1 z.1.2)
  exact (continuous_squareHaarIntegral h).comp continuous_subtype_val

theorem continuous_densityTarget : Continuous densityTarget :=
  continuous_densityTargetProbability.subtype_mk _



end BenchmarkJump
end
end Source42
end BenchmarkJumpSubmission

/- Preserved source skeleton: HaarUnitCoordinateContinuity -/
namespace BenchmarkJumpSubmission
section Source43
open Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

/-- On the unit sphere of real ℓ², continuous coordinates imply norm
continuity. The proof uses finite-coordinate approximation and Cauchy--Schwarz. -/
theorem continuous_haarCoefficients_of_unit_coordinates {X : Type*} [TopologicalSpace X]
    (F : X → HaarCoefficientSpace) (hNorm : ∀ x, ‖F x‖ = 1)
    (hCoord : ∀ i : Option HaarNodeIndex, Continuous (fun x => F x i)) : Continuous F := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ : ℝ := ε ^ 2 / 16
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc (F x₀)) δ hδ).exists
  let b : HaarCoefficientSpace := haarCoefficientTrunc s (F x₀)
  have hb : ‖F x₀ - b‖ < δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hs
  have hFinite : Continuous (fun x => inner ℝ (F x) b) := by
    change Continuous (fun x => inner ℝ (F x)
      (∑ i ∈ s, lp.single 2 i (F x₀ i)))
    simp only [inner_sum, lp.inner_single_right]
    apply continuous_finsetSum
    intro i _hi
    exact (hCoord i).inner continuous_const
  have hNear := Metric.tendsto_nhds.mp (hFinite.tendsto x₀) δ hδ
  filter_upwards [hNear] with x hx
  have hTailX : |inner ℝ (F x) (F x₀) - inner ℝ (F x) b| ≤ ‖F x₀ - b‖ := by
    rw [← inner_sub_right]
    simpa only [Real.norm_eq_abs, hNorm, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (F x) (F x₀ - b)
  have hTail₀ : |inner ℝ (F x₀) (F x₀) - inner ℝ (F x₀) b| ≤ ‖F x₀ - b‖ := by
    rw [← inner_sub_right]
    simpa only [Real.norm_eq_abs, hNorm, one_mul] using
      norm_inner_le_norm (𝕜 := ℝ) (F x₀) (F x₀ - b)
  have hSelf : inner ℝ (F x₀) (F x₀) = 1 := by
    rw [real_inner_self_eq_norm_sq, hNorm]
    norm_num
  rw [hSelf] at hTail₀
  have hN := norm_sub_sq_real (F x) (F x₀)
  rw [hNorm, hNorm] at hN
  have hxAbs : |inner ℝ (F x) b - inner ℝ (F x₀) b| < δ := hx
  have hSq : ‖F x - F x₀‖ ^ 2 < ε ^ 2 := by
    have h1 := (abs_le.mp hTailX).1
    have h2 := (abs_le.mp hTail₀).2
    have h3 := (abs_lt.mp hxAbs).1
    dsimp [δ] at hb hxAbs h3
    nlinarith
  simpa only [dist_eq_norm] using (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hSq



end BenchmarkJump
end
end Source43
end BenchmarkJumpSubmission

/- Preserved source skeleton: PositiveContinuousSections -/
namespace BenchmarkJumpSubmission
section Source44
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

def continuousDensityVector (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  ContinuousMap.toLp 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ℝ w

theorem continuousDensityVector_coe (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    continuousDensityVector μ w =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)] w :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) _ _

theorem continuousDensityVector_norm_sq (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    ‖continuousDensityVector μ w‖ ^ 2 =
      ∫ x, w x ^ 2 ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousDensityVector_coe μ w] with x hx
  rw [hx]
  simp [pow_two]

theorem continuous_continuousDensityVector_norm (w : C(HaarCantor, ℝ)) :
    Continuous (fun μ : PositiveCylinderProbabilities => ‖continuousDensityVector μ w‖) := by
  have hc := (ProbabilityMeasure.continuous_integral_continuousMap (w * w)).comp
    (continuous_subtype_val : Continuous (fun μ : PositiveCylinderProbabilities =>
      (μ : ProbabilityMeasure HaarCantor)))
  have heq : (fun μ : PositiveCylinderProbabilities =>
      Real.sqrt (∫ x, (w * w) x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))) =
      (fun μ : PositiveCylinderProbabilities => ‖continuousDensityVector μ w‖) := by
    funext μ
    have h := continuousDensityVector_norm_sq μ w
    have hint : (∫ x, (w * w) x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) =
        ‖continuousDensityVector μ w‖ ^ 2 := by
      simpa only [ContinuousMap.mul_apply, pow_two] using h.symm
    rw [hint, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact heq ▸ hc.sqrt

theorem continuousDensityVector_norm_pos (μ : PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x) : 0 < ‖continuousDensityVector μ w‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hzero : continuousDensityVector μ w =ᵐ[((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      fun _ => (0 : ℝ) := by
    rw [hz]
    exact Lp.coeFn_zero _ _ _
  have hf : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor), False := by
    filter_upwards [continuousDensityVector_coe μ w, hzero] with x hx hz
    have hp := hpos x
    rw [← hx, hz] at hp
    exact lt_irrefl _ hp
  obtain ⟨_x, hx⟩ := hf.exists
  exact hx

def normalizedContinuousVector (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) :
    Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  ‖continuousDensityVector μ w‖⁻¹ • continuousDensityVector μ w

theorem normalizedContinuousVector_norm (μ : PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x) : ‖normalizedContinuousVector μ w‖ = 1 := by
  have hn := continuousDensityVector_norm_pos μ w hpos
  rw [normalizedContinuousVector, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

def continuousSectionCoefficients (w : C(HaarCantor, ℝ)) (μ : PositiveCylinderProbabilities) :
    HaarCoefficientSpace := (cantorRealHaarBasis μ).repr (normalizedContinuousVector μ w)

theorem continuousSectionCoefficients_norm (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) : ‖continuousSectionCoefficients w μ‖ = 1 := by
  rw [continuousSectionCoefficients, LinearIsometryEquiv.norm_map,
    normalizedContinuousVector_norm μ w hpos]

theorem continuous_haar_inner_fixed (w : C(HaarCantor, ℝ)) (i : Option HaarNodeIndex) :
    Continuous (fun μ : PositiveCylinderProbabilities =>
      inner ℝ (cantorHaarFamily μ i) (continuousDensityVector μ w)) := by
  let F : PositiveCylinderProbabilities → C(HaarCantor, ℝ) := fun μ =>
    ⟨fun x => haarFamilyFunction μ i x * w x,
      ((continuous_haarFamilyFunction i).comp (continuous_const.prodMk continuous_id)).mul w.continuous⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    ((continuous_haarFamilyFunction i).mul (w.continuous.comp continuous_snd))
  have hc := BenchmarkIntegration.continuous_probability_integral.comp
    (continuous_subtype_val.prodMk hF)
  have heq : (fun μ : PositiveCylinderProbabilities =>
      ∫ x, F μ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) =
      (fun μ : PositiveCylinderProbabilities =>
        inner ℝ (cantorHaarFamily μ i) (continuousDensityVector μ w)) := by
    funext μ
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [haarFamilyFunction_coe μ i, continuousDensityVector_coe μ w] with x hx hy
    rw [hx, hy]
    simp only [F, Real.inner_apply]
    rfl
  change Continuous (fun μ : PositiveCylinderProbabilities =>
    ∫ x, F μ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) at hc
  rwa [heq] at hc

/-- Normalized positive continuous functions give genuine continuous
sections of the weak×Hilbert-coefficient density bundle. -/
theorem continuous_continuousSectionCoefficients (w : C(HaarCantor, ℝ))
    (hpos : ∀ x, 0 < w x) : Continuous (continuousSectionCoefficients w) := by
  apply continuous_haarCoefficients_of_unit_coordinates _ (continuousSectionCoefficients_norm w hpos)
  intro i
  have hformula : (fun μ : PositiveCylinderProbabilities => continuousSectionCoefficients w μ i) =
      (fun μ : PositiveCylinderProbabilities => ‖continuousDensityVector μ w‖⁻¹ *
        inner ℝ (cantorHaarFamily μ i) (continuousDensityVector μ w)) := by
    funext μ
    rw [continuousSectionCoefficients, HilbertBasis.repr_apply_apply, normalizedContinuousVector,
      real_inner_smul_right, cantorRealHaarBasis_apply]
  rw [hformula]
  exact ((continuous_continuousDensityVector_norm w).inv₀
    (fun μ => (continuousDensityVector_norm_pos μ w hpos).ne')).mul
      (continuous_haar_inner_fixed w i)

def positiveContinuousSection (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) : PositiveDensityBundle :=
  ⟨(μ, continuousSectionCoefficients w μ), by
    constructor
    · have hlift : haarLift μ (continuousSectionCoefficients w μ) = normalizedContinuousVector μ w :=
        (cantorRealHaarBasis μ).repr.symm_apply_apply _
      change ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
        0 < haarLift μ (continuousSectionCoefficients w μ) x
      rw [hlift]
      filter_upwards [Lp.coeFn_smul ‖continuousDensityVector μ w‖⁻¹ (continuousDensityVector μ w),
        continuousDensityVector_coe μ w] with x hx hy
      change 0 < (‖continuousDensityVector μ w‖⁻¹ • continuousDensityVector μ w) x
      simp only [Pi.smul_apply, smul_eq_mul] at hx
      rw [hx, hy]
      exact mul_pos (inv_pos.mpr (continuousDensityVector_norm_pos μ w hpos)) (hpos x)
    · exact continuousSectionCoefficients_norm w hpos μ⟩

theorem continuous_positiveContinuousSection (w : C(HaarCantor, ℝ)) (hpos : ∀ x, 0 < w x) :
    Continuous (positiveContinuousSection w hpos) :=
  (continuous_id.prodMk (continuous_continuousSectionCoefficients w hpos)).subtype_mk _

@[simp] theorem densitySource_positiveContinuousSection (w : C(HaarCantor, ℝ))
    (hpos : ∀ x, 0 < w x) (μ : PositiveCylinderProbabilities) :
    densitySource (positiveContinuousSection w hpos μ) = μ := rfl



end BenchmarkJump
end
end Source44
end BenchmarkJumpSubmission

/- Preserved source skeleton: PositiveSectionDensity -/
namespace BenchmarkJumpSubmission
section Source45
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem normalize_dist_le_twice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g f : E) (hg : g ≠ 0) (hf : ‖f‖ = 1) :
    dist (‖g‖⁻¹ • g) f ≤ 2 * dist g f := by
  have hn : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hscale : dist (‖g‖⁻¹ • g) g = |1 - ‖g‖| := by
    rw [dist_eq_norm]
    have heq : ‖g‖⁻¹ • g - g = (‖g‖⁻¹ - 1) • g := by module
    rw [heq, norm_smul, Real.norm_eq_abs]
    calc
      |‖g‖⁻¹ - 1| * ‖g‖ = |(‖g‖⁻¹ - 1) * ‖g‖| := by
        rw [abs_mul, abs_of_pos hn]
      _ = |1 - ‖g‖| := by congr 1; field_simp
  have hrev : |1 - ‖g‖| ≤ dist g f := by
    simpa only [hf, abs_sub_comm, dist_eq_norm] using abs_norm_sub_norm_le g f
  have ht := dist_triangle (‖g‖⁻¹ • g) g f
  rw [hscale] at ht
  linarith

/-- Strictly-positive continuous functions, normalized in L2, are dense
among positive unit densities for the genuine Cantor measure. -/
theorem positive_continuous_vectors_dense (μ : PositiveCylinderProbabilities)
    (f : Lp ℝ 2 ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hPos : ∀ᵐ x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor), 0 < f x)
    (hNorm : ‖f‖ = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ w : C(HaarCantor, ℝ), (∀ x, 0 < w x) ∧ dist (normalizedContinuousVector μ w) f < ε := by
  let ν : Measure HaarCantor := ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  let η : ℝ := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  have hd : DenseRange (ContinuousMap.toLp 2 ν ℝ : C(HaarCantor, ℝ) →L[ℝ] Lp ℝ 2 ν) :=
    ContinuousMap.toLp_denseRange _ _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  obtain ⟨v, hv⟩ := hd.exists_dist_lt f hη
  let ψ : ℝ → ℝ := fun t => max t 0
  have hψ : LipschitzWith 1 ψ := LipschitzWith.id.max_const 0
  have hψ0 : ψ 0 = 0 := by simp [ψ]
  let w : C(HaarCantor, ℝ) :=
    ⟨fun x => max (v x) 0 + η, (v.continuous.max continuous_const).add continuous_const⟩
  have hwPos : ∀ x, 0 < w x := by
    intro x
    exact add_pos_of_nonneg_of_pos (le_max_right _ _) hη
  have hFix : hψ.compLp hψ0 f = f := by
    apply Lp.ext
    filter_upwards [hψ.coeFn_compLp hψ0 f, hPos] with x hx hp
    simpa only [ψ, Function.comp_apply, max_eq_left hp.le] using hx
  have hwEq : continuousDensityVector μ w =
      hψ.compLp hψ0 (continuousDensityVector μ v) + η • cantorOneVector μ := by
    apply Lp.ext
    filter_upwards [continuousDensityVector_coe μ w,
      Lp.coeFn_add (hψ.compLp hψ0 (continuousDensityVector μ v)) (η • cantorOneVector μ),
      hψ.coeFn_compLp hψ0 (continuousDensityVector μ v),
      Lp.coeFn_smul η (cantorOneVector μ), haarFamilyFunction_coe μ none,
      continuousDensityVector_coe μ v] with x hw ha hc hs h1 hv
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at ha hc hs
    change cantorOneVector μ x = 1 at h1
    rw [hw, ha, hc, hs, h1, hv]
    simp only [w, ψ, mul_one]
    rfl
  have hComp : ‖hψ.compLp hψ0 (continuousDensityVector μ v) - f‖ ≤
      ‖continuousDensityVector μ v - f‖ := by
    have h := hψ.norm_compLp_sub_le hψ0 (continuousDensityVector μ v) f
    simpa only [hFix, NNReal.coe_one, one_mul] using h
  have hOne : ‖η • cantorOneVector μ‖ = η := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, cantorOneVector_norm, mul_one]
  have hErr : dist (continuousDensityVector μ w) f < 2 * η := by
    rw [dist_eq_norm, hwEq]
    have heq : hψ.compLp hψ0 (continuousDensityVector μ v) + η • cantorOneVector μ - f =
        (hψ.compLp hψ0 (continuousDensityVector μ v) - f) + η • cantorOneVector μ := by module
    rw [heq]
    have ht := norm_add_le (hψ.compLp hψ0 (continuousDensityVector μ v) - f) (η • cantorOneVector μ)
    rw [hOne] at ht
    rw [dist_comm] at hv
    change dist (continuousDensityVector μ v) f < η at hv
    rw [dist_eq_norm] at hv
    linarith
  have hn := continuousDensityVector_norm_pos μ w hwPos
  refine ⟨w, hwPos, ?_⟩
  have hBound := normalize_dist_le_twice (continuousDensityVector μ w) f
    (norm_pos_iff.mp hn) hNorm
  change dist (‖continuousDensityVector μ w‖⁻¹ • continuousDensityVector μ w) f < ε
  dsimp [η] at hErr
  linarith

/-- At any bundle point, values of the proved continuous positive sections
are norm dense in its source fiber. -/
theorem positiveContinuousSection_fiber_dense (z : PositiveDensityBundle)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ w : C(HaarCantor, ℝ), ∃ hpos : ∀ x, 0 < w x,
      dist (continuousSectionCoefficients w (densitySource z)) z.1.2 < ε := by
  obtain ⟨w, hw, hNear⟩ := positive_continuous_vectors_dense (densitySource z)
    (densityVector z) (densityVector_positive z) (densityVector_norm z) ε hε
  refine ⟨w, hw, ?_⟩
  have hrepr : (cantorRealHaarBasis (densitySource z)).repr (densityVector z) = z.1.2 :=
    (cantorRealHaarBasis (densitySource z)).repr.apply_symm_apply _
  have hdist := (cantorRealHaarBasis (densitySource z)).repr.isometry.dist_eq
    (normalizedContinuousVector (densitySource z) w) (densityVector z)
  change dist ((cantorRealHaarBasis (densitySource z)).repr
    (normalizedContinuousVector (densitySource z) w)) z.1.2 < ε
  rw [← hrepr, hdist]
  exact hNear



end BenchmarkJump
end
end Source45
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensitySourceOpen -/
namespace BenchmarkJumpSubmission
section Source46
open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- The source projection of the genuine positive square-density bundle is open.
The proof uses the proved density and continuity of positive continuous sections. -/
theorem isOpenMap_densitySource : IsOpenMap densitySource := by
  intro W hW
  apply isOpen_iff_mem_nhds.mpr
  rintro μ ⟨z, hzW, rfl⟩
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hW
  have hzV : z.1 ∈ V := by
    change z ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hzW
  obtain ⟨U, A, hUo, hAo, hμU, haA, hUA⟩ :=
    isOpen_prod_iff.mp hVo z.1.1 z.1.2 hzV
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hAo z.1.2 haA
  obtain ⟨w, hw, hNear⟩ := positiveContinuousSection_fiber_dense z ε hε
  have hsecW : positiveContinuousSection w hw (densitySource z) ∈ W := by
    rw [← hVW]
    exact hUA ⟨hμU, hBall hNear⟩
  have hN := (hW.preimage (continuous_positiveContinuousSection w hw)).mem_nhds hsecW
  exact mem_of_superset hN (fun ν hν =>
    ⟨positiveContinuousSection w hw ν, hν, densitySource_positiveContinuousSection w hw ν⟩)

theorem densitySource_surjective : Function.Surjective densitySource := by
  intro μ
  exact ⟨positiveContinuousSection 1 (by intro x; norm_num) μ,
    densitySource_positiveContinuousSection 1 (by intro x; norm_num) μ⟩



end BenchmarkJump
end
end Source46
end BenchmarkJumpSubmission

/- Preserved source skeleton: LinearHaarIntegralContinuity -/
namespace BenchmarkJumpSubmission
section Source47
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators

noncomputable section

namespace BenchmarkJump

theorem continuousDensityVector_norm_le (μ : PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) : ‖continuousDensityVector μ w‖ ≤ ‖w‖ := by
  have hOp : ‖(ContinuousMap.toLp 2
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ℝ :
      C(HaarCantor, ℝ) →L[ℝ] Lp ℝ 2
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))‖ ≤ 1 := by
    simpa [measureUnivNNReal] using ContinuousMap.toLp_norm_le (p := (2 : ℝ≥0∞))
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (𝕜 := ℝ) (E := ℝ)
  exact (ContinuousLinearMap.le_opNorm _ w).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hOp (norm_nonneg w))

def linearHaarIntegral (w : C(HaarCantor, ℝ)) (μ : PositiveCylinderProbabilities)
    (a : HaarCoefficientSpace) : ℝ := inner ℝ (continuousDensityVector μ w) (haarLift μ a)

theorem linearHaarIntegral_eq_integral (w : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    linearHaarIntegral w μ a =
      ∫ x, w x * haarLift μ a x ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [linearHaarIntegral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousDensityVector_coe μ w] with x hx
  rw [hx, Real.inner_apply, mul_comm]

theorem linearHaarIntegral_coefficient_dist_le (w : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a b : HaarCoefficientSpace) :
    dist (linearHaarIntegral w μ a) (linearHaarIntegral w μ b) ≤ ‖w‖ * dist a b := by
  rw [linearHaarIntegral, linearHaarIntegral, dist_eq_norm, ← inner_sub_right]
  calc
    _ ≤ ‖continuousDensityVector μ w‖ * ‖haarLift μ a - haarLift μ b‖ :=
      norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ ‖w‖ * ‖haarLift μ a - haarLift μ b‖ :=
      mul_le_mul_of_nonneg_right (continuousDensityVector_norm_le μ w) (norm_nonneg _)
    _ = _ := by rw [← dist_eq_norm, dist_haarLift]

theorem linearHaarIntegral_test_dist_le (w v : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (a : HaarCoefficientSpace) :
    dist (linearHaarIntegral w μ a) (linearHaarIntegral v μ a) ≤ dist w v * ‖a‖ := by
  rw [linearHaarIntegral, linearHaarIntegral, dist_eq_norm, ← inner_sub_left]
  have hSub : continuousDensityVector μ w - continuousDensityVector μ v =
      continuousDensityVector μ (w - v) := (map_sub _ w v).symm
  rw [hSub]
  calc
    _ ≤ ‖continuousDensityVector μ (w - v)‖ * ‖haarLift μ a‖ :=
      norm_inner_le_norm (𝕜 := ℝ) _ _
    _ ≤ ‖w - v‖ * ‖haarLift μ a‖ :=
      mul_le_mul_of_nonneg_right (continuousDensityVector_norm_le μ (w - v)) (norm_nonneg _)
    _ = _ := by rw [dist_eq_norm, norm_haarLift]

theorem linearHaarIntegral_trunc_eq (w : C(HaarCantor, ℝ))
    (μ : PositiveCylinderProbabilities) (s : Finset (Option HaarNodeIndex))
    (a : HaarCoefficientSpace) :
    linearHaarIntegral w μ (haarCoefficientTrunc s a) =
      ∫ x, w x * finiteHaarFunction s μ a x
        ∂((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  rw [linearHaarIntegral_eq_integral]
  apply integral_congr_ae
  filter_upwards [haarLift_trunc_coe μ s a] with x hx
  rw [hx]

theorem continuous_linearHaarIntegral_trunc (w : C(HaarCantor, ℝ))
    (s : Finset (Option HaarNodeIndex)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      linearHaarIntegral w p.1 (haarCoefficientTrunc s p.2)) := by
  let F : (PositiveCylinderProbabilities × HaarCoefficientSpace) → C(HaarCantor, ℝ) := fun p =>
    ⟨fun x => w x * finiteHaarFunction s p.1 p.2 x,
      w.continuous.mul ((continuous_finiteHaarFunction s).comp
        (continuous_const.prodMk continuous_id))⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    ((w.continuous.comp continuous_snd).mul (continuous_finiteHaarFunction s))
  have hc := BenchmarkIntegration.continuous_probability_integral.comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hF)
  change Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
    ∫ x, w x * finiteHaarFunction s p.1 p.2 x
      ∂((p.1 : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) at hc
  simpa only [linearHaarIntegral_trunc_eq] using hc

theorem continuous_linearHaarIntegral (w : C(HaarCantor, ℝ)) :
    Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      linearHaarIntegral w p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := ‖w‖ + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hwL : ‖w‖ ≤ L := by dsimp [L]; linarith
  let δ : ℝ := ε / (8 * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨s, hs⟩ := (Metric.tendsto_nhds.mp (tendsto_haarCoefficientTrunc p₀.2) δ hδ).exists
  let b := haarCoefficientTrunc s p₀.2
  have hb : dist b p₀.2 < δ := hs
  have hFixed : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace =>
      linearHaarIntegral w p.1 b) :=
    (continuous_linearHaarIntegral_trunc w s).comp
      (continuous_fst.prodMk (continuous_const (y := p₀.2)))
  have hNearF := Metric.tendsto_nhds.mp (hFixed.tendsto p₀) (ε / 2) (by positivity)
  have hNearA := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : PositiveCylinderProbabilities × HaarCoefficientSpace => p.2)).tendsto p₀)
      δ hδ
  filter_upwards [hNearF, hNearA] with p hpF hpA
  have hTri := dist_triangle (linearHaarIntegral w p.1 p.2)
    (linearHaarIntegral w p.1 b) (linearHaarIntegral w p₀.1 p₀.2)
  have hTri2 := dist_triangle (linearHaarIntegral w p.1 b)
    (linearHaarIntegral w p₀.1 b) (linearHaarIntegral w p₀.1 p₀.2)
  have hA := linearHaarIntegral_coefficient_dist_le w p.1 p.2 b
  have hB := linearHaarIntegral_coefficient_dist_le w p₀.1 b p₀.2
  have hAB : dist p.2 b ≤ dist p.2 p₀.2 + dist b p₀.2 := by
    simpa only [dist_comm b p₀.2] using dist_triangle p.2 p₀.2 b
  have hA' : ‖w‖ * dist p.2 b ≤ L * (dist p.2 p₀.2 + dist b p₀.2) :=
    mul_le_mul hwL hAB dist_nonneg hL.le
  have hB' : ‖w‖ * dist b p₀.2 ≤ L * dist b p₀.2 :=
    mul_le_mul_of_nonneg_right hwL dist_nonneg
  have hCalc : L * δ = ε / 8 := by dsimp [δ]; field_simp
  nlinarith

theorem continuous_linearHaarIntegral_joint :
    Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) × C(HaarCantor, ℝ) =>
      linearHaarIntegral p.2 p.1.1 p.1.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L : ℝ := ‖p₀.1.2‖ + 2
  have hL : 0 < L := by dsimp [L]; positivity
  have hA := Metric.tendsto_nhds.mp
    ((continuous_snd.comp continuous_fst :
      Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) ×
        C(HaarCantor, ℝ) => p.1.2)).tendsto p₀) 1 (by norm_num)
  have hW := Metric.tendsto_nhds.mp
    ((continuous_snd : Continuous (fun p : (PositiveCylinderProbabilities × HaarCoefficientSpace) ×
      C(HaarCantor, ℝ) => p.2)).tendsto p₀) (ε / (2 * L)) (by positivity)
  have hF := Metric.tendsto_nhds.mp
    (((continuous_linearHaarIntegral p₀.2).comp continuous_fst).tendsto p₀)
      (ε / 2) (by positivity)
  filter_upwards [hA, hW, hF] with p hpA hpW hpF
  change dist p.1.2 p₀.1.2 < 1 at hpA
  change dist (linearHaarIntegral p₀.2 p.1.1 p.1.2)
    (linearHaarIntegral p₀.2 p₀.1.1 p₀.1.2) < ε / 2 at hpF
  have hN : ‖p.1.2‖ ≤ L := by
    have hn : ‖p.1.2‖ ≤ dist p.1.2 p₀.1.2 + ‖p₀.1.2‖ := by
      simpa only [dist_zero_right] using dist_triangle p.1.2 p₀.1.2 0
    dsimp [L]
    linarith
  have hB := linearHaarIntegral_test_dist_le p.2 p₀.2 p.1.1 p.1.2
  have hB' : dist p.2 p₀.2 * ‖p.1.2‖ ≤ dist p.2 p₀.2 * L :=
    mul_le_mul_of_nonneg_left hN dist_nonneg
  have hSmall := mul_lt_mul_of_pos_right hpW hL
  have he : ε / (2 * L) * L = ε / 2 := by field_simp
  have hTri := dist_triangle (linearHaarIntegral p.2 p.1.1 p.1.2)
    (linearHaarIntegral p₀.2 p.1.1 p.1.2) (linearHaarIntegral p₀.2 p₀.1.1 p₀.1.2)
  linarith



end BenchmarkJump
end
end Source47
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityInverseContinuity -/
namespace BenchmarkJumpSubmission
section Source48
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def haarFamilyContinuousMap (μ : PositiveCylinderProbabilities) (i : Option HaarNodeIndex) :
    C(HaarCantor, ℝ) :=
  ⟨haarFamilyFunction μ i,
    (continuous_haarFamilyFunction i).comp (continuous_const.prodMk continuous_id)⟩

theorem continuous_haarFamilyContinuousMap (i : Option HaarNodeIndex) :
    Continuous (fun μ : PositiveCylinderProbabilities => haarFamilyContinuousMap μ i) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_haarFamilyFunction i)

theorem densityInverseCoefficients_formula (z : PositiveDensityBundle) (i : Option HaarNodeIndex) :
    densityInverseCoefficients z i =
      linearHaarIntegral (haarFamilyContinuousMap (densityTarget z) i)
        (densitySource z) z.1.2 := by
  rw [densityInverseCoefficients, HilbertBasis.repr_apply_apply,
    cantorRealHaarBasis_apply, L2.inner_def]
  calc
    _ = ∫ x, haarFamilyFunction (densityTarget z) i x * inverseDensityVector z x
        ∂((densityTarget z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
      apply integral_congr_ae
      filter_upwards [haarFamilyFunction_coe (densityTarget z) i] with x hx
      rw [hx, Real.inner_apply, mul_comm]
    _ = ∫ x, haarFamilyFunction (densityTarget z) i x * densityVector z x
        ∂((densitySource z : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
      integral_inverseDensityVector z _
    _ = _ := (linearHaarIntegral_eq_integral (haarFamilyContinuousMap (densityTarget z) i)
      (densitySource z) z.1.2).symm

theorem continuous_densityInverseCoefficients : Continuous densityInverseCoefficients := by
  apply continuous_haarCoefficients_of_unit_coordinates _
    (fun z => by rw [densityInverseCoefficients, LinearIsometryEquiv.norm_map,
      inverseDensityVector_norm])
  intro i
  have hc := continuous_linearHaarIntegral_joint.comp
    ((continuous_densitySource.prodMk (continuous_snd.comp continuous_subtype_val)).prodMk
      ((continuous_haarFamilyContinuousMap i).comp continuous_densityTarget))
  change Continuous (fun z : PositiveDensityBundle =>
    linearHaarIntegral (haarFamilyContinuousMap (densityTarget z) i)
      (densitySource z) z.1.2) at hc
  simpa only [← densityInverseCoefficients_formula] using hc

theorem continuous_densityInverse : Continuous densityInverse :=
  (continuous_densityTarget.prodMk continuous_densityInverseCoefficients).subtype_mk _

def densityInverseHomeomorph : PositiveDensityBundle ≃ₜ PositiveDensityBundle :=
  { toEquiv := densityInverse_involutive.toPerm densityInverse
    continuous_toFun := continuous_densityInverse
    continuous_invFun := continuous_densityInverse }

/-- The genuine target projection is open, by the proved continuous
inversion homeomorphism and openness of the source projection. -/
theorem isOpenMap_densityTarget : IsOpenMap densityTarget := by
  have heq : densityTarget = densitySource ∘ densityInverse := rfl
  rw [heq]
  exact isOpenMap_densitySource.comp densityInverseHomeomorph.isOpenMap




end BenchmarkJump
end
end Source48
end BenchmarkJumpSubmission

/- Preserved source skeleton: JumpRows -/
namespace BenchmarkJumpSubmission
section Source49
/-! The common category lemma used in both jump-obstruction proofs of
`Benchmark.tex`.  This file proves the category and row-support argument.
It does not assert either of the two obstruction theorems: obtaining the
local row hypothesis for their two concrete source spaces is separate work. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*}

/-- The Friedman--Stanley jump records precisely the countable set of row classes. -/
def Jump (R : Y → Y → Prop) (u v : ℕ → Y) : Prop :=
  (∀ k, ∃ l, R (u k) (v l)) ∧ (∀ l, ∃ k, R (u k) (v l))

def Homomorphism (E : X → X → Prop) (R : Y → Y → Prop) (F : X → Y) : Prop :=
  ∀ x y, E x y → R (F x) (F y)

variable [TopologicalSpace X]

/-- Generic ergodicity, stated for invariant sets with the Baire property. -/
def GenericallyErgodic (E : X → X → Prop) : Prop :=
  ∀ s : Set X, BaireMeasurableSet s →
    (∀ x y, E x y → (x ∈ s ↔ y ∈ s)) →
    IsMeagre s ∨ s ∈ residual X

/-- Local constancy is comeagerness relative to the open set, expressed as
an eventual implication in the ambient residual filter. -/
def LocallyGenericallyConstantRows (R : Y → Y → Prop)
    (F : X → ℕ → Y) : Prop :=
  ∀ k (A : Set X), IsOpen A → A.Nonempty →
    ∃ O : Set X, ∃ a : Y, IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧
      ∀ᶠ x in residual X, x ∈ O → R (F x k) a

/-- A countable basis turns the local row hypothesis into a single countable
family containing all row classes at comeager many source points. -/
theorem countable_row_representatives [SecondCountableTopology X]
    (R : Y → Y → Prop) (F : X → ℕ → Y)
    (hloc : LocallyGenericallyConstantRows R F) :
    ∃ a : ℕ × countableBasis X → Y,
      ∀ᶠ x in residual X, ∀ k, ∃ r, R (F x k) (a r) := by
  classical
  choose O a hOo hOn hOs hOres using fun (k : ℕ) (B : countableBasis X) =>
    hloc k B (isOpen_of_mem_countableBasis B.property)
      (nonempty_of_mem_countableBasis B.property)
  have hDense (k : ℕ) : Dense (⋃ B, O k B) := by
    apply dense_iff_inter_open.2
    intro U hU hUn
    obtain ⟨x, hx⟩ := hUn
    obtain ⟨B, hB, _hxB, hBU⟩ :=
      (isBasis_countableBasis X).exists_subset_of_mem_open hx hU
    obtain ⟨y, hy⟩ := hOn k ⟨B, hB⟩
    exact ⟨y, hBU (hOs k ⟨B, hB⟩ hy), mem_iUnion.2 ⟨⟨B, hB⟩, hy⟩⟩
  have hCover : ∀ᶠ x in residual X, ∀ k, x ∈ ⋃ B, O k B :=
    eventually_countable_forall.2 fun k =>
      residual_of_dense_open (isOpen_iUnion (hOo k)) (hDense k)
  have hGood : ∀ᶠ x in residual X, ∀ r : ℕ × countableBasis X,
      x ∈ O r.1 r.2 → R (F x r.1) (a r.1 r.2) :=
    eventually_countable_forall.2 fun r => hOres r.1 r.2
  refine ⟨fun r => a r.1 r.2, ?_⟩
  filter_upwards [hCover, hGood] with x hx hg
  intro k
  obtain ⟨B, hB⟩ := mem_iUnion.1 (hx k)
  exact ⟨(k, B), hg (k, B) hB⟩

/-- Jump homomorphisms preserve the membership of every fixed target class
in their countable set of row classes. -/
theorem row_support_invariant (R : Y → Y → Prop) (hR : Equivalence R)
    (E : X → X → Prop) (F : X → ℕ → Y)
    (hF : Homomorphism E (Jump R) F) (a : Y) :
    ∀ x y, E x y →
      ((∃ k, R (F x k) a) ↔ ∃ k, R (F y k) a) := by
  intro x y hxy
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := (hF x y hxy).1 k
    exact ⟨l, hR.trans (hR.symm hl) hk⟩
  · rintro ⟨l, hl⟩
    obtain ⟨k, hk⟩ := (hF x y hxy).2 l
    exact ⟨k, hR.trans hk hl⟩

/-- Countably many Baire invariant coordinates are simultaneously constant
on one comeager set. -/
theorem invariant_coordinates_constant {ι : Type*} [Countable ι]
    (E : X → X → Prop) (hE : GenericallyErgodic E)
    (P : ι → X → Prop)
    (hP : ∀ i, BaireMeasurableSet {x | P i x})
    (hInv : ∀ i x y, E x y → (P i x ↔ P i y)) :
    ∃ b : ι → Bool, ∀ᶠ x in residual X, ∀ i, P i x ↔ b i = true := by
  classical
  have hOne (i : ι) : ∃ b : Bool,
      ∀ᶠ x in residual X, P i x ↔ b = true := by
    rcases hE {x | P i x} (hP i) (hInv i) with hm | hr
    · refine ⟨false, ?_⟩
      filter_upwards [hm] with x hx
      simp only [mem_compl_iff, mem_setOf_eq] at hx
      simp [hx]
    · refine ⟨true, ?_⟩
      filter_upwards [hr] with x hx
      simpa using hx
  choose b hb using hOne
  exact ⟨b, eventually_countable_forall.2 hb⟩

/-- The countable-class part of the row lemma, after the countable basis
argument has produced representatives. -/
theorem generically_constant_of_representatives {ι : Type*} [Countable ι]
    [Nonempty X] [BaireSpace X]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (F : X → ℕ → Y) (hF : Homomorphism E (Jump R) F)
    (hE : GenericallyErgodic E) (a : ι → Y)
    (hRep : ∀ᶠ x in residual X, ∀ k, ∃ r, R (F x k) (a r))
    (hBaire : ∀ r, BaireMeasurableSet {x | ∃ k, R (F x k) (a r)}) :
    ∃ v : ℕ → Y, ∀ᶠ x in residual X, Jump R (F x) v := by
  obtain ⟨b, hb⟩ := invariant_coordinates_constant E hE
    (fun r x => ∃ k, R (F x k) (a r)) hBaire
    (fun r => row_support_invariant R hR E F hF (a r))
  obtain ⟨x₀, hxRep, hxBool⟩ := (dense_of_mem_residual (hRep.and hb)).nonempty
  refine ⟨F x₀, ?_⟩
  filter_upwards [hRep, hb] with x hxR hxb
  constructor
  · intro k
    obtain ⟨r, hr⟩ := hxR k
    have hrb : b r = true := (hxb r).mp ⟨k, hr⟩
    obtain ⟨l, hl⟩ := (hxBool r).mpr hrb
    exact ⟨l, hR.trans hr (hR.symm hl)⟩
  · intro l
    obtain ⟨r, hr⟩ := hxRep l
    have hrb : b r = true := (hxBool r).mp ⟨l, hr⟩
    obtain ⟨k, hk⟩ := (hxb r).mpr hrb
    exact ⟨k, hR.trans hk (hR.symm hr)⟩

/-- Borel row maps and a Borel target relation give Baire measurable
class-support coordinates, as required by generic ergodicity. -/
theorem row_support_baire [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (R : Y → Y → Prop) (hR : MeasurableSet {p : Y × Y | R p.1 p.2})
    (F : X → ℕ → Y) (hF : Measurable F) (a : Y) :
    BaireMeasurableSet {x | ∃ k, R (F x k) a} := by
  apply MeasurableSet.baireMeasurableSet
  have hOne (k : ℕ) : MeasurableSet {x | R (F x k) a} :=
    hR.preimage (((measurable_pi_apply k).comp hF).prodMk measurable_const)
  simpa only [setOf_exists] using MeasurableSet.iUnion hOne

/-- Lemma `rows` of the manuscript, with its Borel and topology assumptions
made explicit. This proves the common row-to-jump category implication in full. -/
theorem locally_constant_rows_imp_constant_jump
    [SecondCountableTopology X] [Nonempty X] [BaireSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hRBorel : MeasurableSet {p : Y × Y | R p.1 p.2})
    (F : X → ℕ → Y) (hFmeas : Measurable F)
    (hF : Homomorphism E (Jump R) F) (hE : GenericallyErgodic E)
    (hloc : LocallyGenericallyConstantRows R F) :
    ∃ v : ℕ → Y, ∀ᶠ x in residual X, Jump R (F x) v := by
  obtain ⟨a, ha⟩ := countable_row_representatives R F hloc
  exact generically_constant_of_representatives E R hR F hF hE a ha
    (fun r => row_support_baire R hRBorel F hFmeas (a r))

theorem jump_equivalence (R : Y → Y → Prop) (hR : Equivalence R) :
    Equivalence (Jump R) := by
  constructor
  · intro x
    exact ⟨fun k => ⟨k, hR.refl _⟩, fun k => ⟨k, hR.refl _⟩⟩
  · intro x y hxy
    exact ⟨fun k => (hxy.2 k).imp fun l hl => hR.symm hl,
      fun l => (hxy.1 l).imp fun k hk => hR.symm hk⟩
  · intro x y z hxy hyz
    constructor
    · intro k
      obtain ⟨l, hl⟩ := hxy.1 k
      obtain ⟨m, hm⟩ := hyz.1 l
      exact ⟨m, hR.trans hl hm⟩
    · intro m
      obtain ⟨l, hl⟩ := hyz.2 m
      obtain ⟨k, hk⟩ := hxy.2 l
      exact ⟨k, hR.trans hk hl⟩

/-- A relation with meager classes cannot have a reduction that is constant
modulo the target on a comeager set. No descriptive-set-theoretic obstruction
is assumed in this implication. -/
theorem not_reduction_of_generic_constancy [Nonempty X] [BaireSpace X]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hClasses : ∀ x, IsMeagre {y | E y x})
    (F : X → Y) (hConst : ∃ v, ∀ᶠ x in residual X, R (F x) v) :
    ¬ (∀ x y, E x y ↔ R (F x) (F y)) := by
  intro hRed
  obtain ⟨v, hv⟩ := hConst
  obtain ⟨x₀, hx₀⟩ := (dense_of_mem_residual hv).nonempty
  have hClass : {y | R (F y) v} ⊆ {y | E y x₀} := by
    intro y hy
    exact (hRed y x₀).mpr (hR.trans hy (hR.symm hx₀))
  exact not_isMeagre_of_mem_residual hv ((hClasses x₀).mono hClass)

/-- The general reduction obstruction after local row constancy and
generic ergodicity have been proved for a concrete source. -/
theorem not_borel_reduction_of_local_rows
    [SecondCountableTopology X] [Nonempty X] [BaireSpace X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y]
    (E : X → X → Prop) (R : Y → Y → Prop) (hR : Equivalence R)
    (hRBorel : MeasurableSet {p : Y × Y | R p.1 p.2})
    (hE : GenericallyErgodic E) (hClasses : ∀ x, IsMeagre {y | E y x})
    (hLocal : ∀ F : X → ℕ → Y, Measurable F →
      Homomorphism E (Jump R) F → LocallyGenericallyConstantRows R F) :
    ¬ ∃ F : X → ℕ → Y, Measurable F ∧
      ∀ x y, E x y ↔ Jump R (F x) (F y) := by
  rintro ⟨F, hFm, hRed⟩
  have hF : Homomorphism E (Jump R) F := fun x y h => (hRed x y).mp h
  have hConst := locally_constant_rows_imp_constant_jump E R hR hRBorel F hFm hF hE
    (hLocal F hFm hF)
  exact not_reduction_of_generic_constancy E (Jump R) (jump_equivalence R hR)
    hClasses F hConst hRed




end BenchmarkJump
end Source49
end BenchmarkJumpSubmission

/- Preserved source skeleton: BoundedDifferenceJump -/
namespace BenchmarkJumpSubmission
section Source50
/-! The actual bounded-difference relation and its Friedman--Stanley jump,
including the Borel facts and closed exhaustion used in the manuscript. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

abbrev RealSequences := ℕ → ℝ

def UniformBound (n : ℕ) (x y : RealSequences) : Prop :=
  ∀ i, |x i - y i| ≤ (n : ℝ)

def BoundedDifference (x y : RealSequences) : Prop :=
  ∃ n : ℕ, UniformBound n x y

theorem uniformBound_refl (x : RealSequences) : UniformBound 0 x x := by
  intro i
  simp

theorem uniformBound_symm {n : ℕ} {x y : RealSequences}
    (h : UniformBound n x y) : UniformBound n y x := by
  intro i
  simpa only [abs_sub_comm] using h i

theorem uniformBound_trans {n m : ℕ} {x y z : RealSequences}
    (hxy : UniformBound n x y) (hyz : UniformBound m y z) :
    UniformBound (n + m) x z := by
  intro i
  calc
    |x i - z i| ≤ |x i - y i| + |y i - z i| := abs_sub_le _ _ _
    _ ≤ (n : ℝ) + m := add_le_add (hxy i) (hyz i)
    _ = ((n + m : ℕ) : ℝ) := by norm_cast

theorem boundedDifference_equivalence : Equivalence BoundedDifference := by
  constructor
  · intro x
    exact ⟨0, uniformBound_refl x⟩
  · rintro x y ⟨n, h⟩
    exact ⟨n, uniformBound_symm h⟩
  · rintro x y z ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, uniformBound_trans hn hm⟩

theorem isClosed_uniformBound (n : ℕ) :
    IsClosed {p : RealSequences × RealSequences | UniformBound n p.1 p.2} := by
  change IsClosed {p : RealSequences × RealSequences | ∀ i, |p.1 i - p.2 i| ≤ (n : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro i
  exact isClosed_le
    ((((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)).abs) continuous_const

theorem measurableSet_boundedDifference :
    MeasurableSet {p : RealSequences × RealSequences | BoundedDifference p.1 p.2} := by
  change MeasurableSet {p : RealSequences × RealSequences | ∃ n, UniformBound n p.1 p.2}
  simpa only [setOf_exists] using
    MeasurableSet.iUnion (fun n => (isClosed_uniformBound n).measurableSet)

theorem boundedDifference_iff_real_bound (x y : RealSequences) :
    BoundedDifference x y ↔ ∃ C : ℝ, ∀ i, |x i - y i| ≤ C := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨C, hC⟩
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact ⟨n, fun i => (hC i).trans hn⟩











end BenchmarkJump
end Source50
end BenchmarkJumpSubmission

/- Preserved source skeleton: CategoryTools -/
namespace BenchmarkJumpSubmission
section Source51
/-! Category tools needed by the concrete jump-obstruction arguments. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A Borel map into a second-countable space is continuous on a dense
Gdelta subspace of any Baire domain. This is relative continuity. -/
theorem measurable_continuousOn_residual
    [BaireSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Measurable f) :
    ∃ D : Set X, IsGδ D ∧ Dense D ∧ ContinuousOn f D := by
  classical
  have hB (B : countableBasis Y) :
      BaireMeasurableSet (f ⁻¹' (B : Set Y)) :=
    (hf (isOpen_of_mem_countableBasis B.property).measurableSet).baireMeasurableSet
  choose U hU hEq using fun B : countableBasis Y => (hB B).residualEq_isOpen
  have hAll : ∀ᶠ x in residual X, ∀ B : countableBasis Y,
      f x ∈ (B : Set Y) ↔ x ∈ U B :=
    eventually_countable_forall.2 fun B => Filter.eventuallyEq_set.mp (hEq B)
  obtain ⟨D, hDG, hDd, hD⟩ := eventually_residual.mp hAll
  refine ⟨D, hDG, hDd, (isBasis_countableBasis Y).continuousOn_iff.mpr ?_⟩
  intro B hB
  refine ⟨U ⟨B, hB⟩, hU _, ?_⟩
  ext x
  constructor
  · rintro ⟨hxB, hxD⟩
    exact ⟨(hD x hxD ⟨B, hB⟩).mp hxB, hxD⟩
  · rintro ⟨hxU, hxD⟩
    exact ⟨(hD x hxD ⟨B, hB⟩).mpr hxU, hxD⟩

/-- The projection of an open relation intersected with a nonempty open
vertical set is open. -/
theorem isOpen_exists_vertical {U : Set (X × Y)} (hU : IsOpen U)
    {V : Set Y} (hV : IsOpen V) :
    IsOpen {x | ∃ y ∈ V, (x, y) ∈ U} := by
  have heq : {x | ∃ y ∈ V, (x, y) ∈ U} =
      Prod.fst '' (U ∩ Prod.snd ⁻¹' V) := by
    ext x
    constructor
    · rintro ⟨y, hyV, hxy⟩
      exact ⟨(x, y), ⟨hxy, hyV⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hxy, hyV⟩, hxx⟩
      change x' = x at hxx
      subst x'
      exact ⟨y, hyV, hxy⟩
  rw [heq]
  exact isOpenMap_fst _ (hU.inter (hV.preimage continuous_snd))

/-- The same projection is dense when the relation is open dense and the
vertical set is nonempty open. -/
theorem dense_exists_vertical {U : Set (X × Y)} (hUd : Dense U)
    {V : Set Y} (hVo : IsOpen V) (hVn : V.Nonempty) :
    Dense {x | ∃ y ∈ V, (x, y) ∈ U} := by
  apply dense_iff_inter_open.mpr
  intro A hAo hAn
  obtain ⟨x, hx⟩ := hAn
  obtain ⟨y, hy⟩ := hVn
  obtain ⟨⟨x', y'⟩, ⟨hxA, hyV⟩, hxyU⟩ :=
    hUd.inter_open_nonempty (A ×ˢ V) (hAo.prod hVo) ⟨(x, y), hx, hy⟩
  exact ⟨x', hxA, y', hyV, hxyU⟩

/-- The residual-set direction of Kuratowski--Ulam, proved from countable
bases and dense open projections. This suffices for the manuscript's use. -/
theorem eventually_residual_prod [SecondCountableTopology Y]
    {P : X × Y → Prop} (hP : ∀ᶠ p in residual (X × Y), P p) :
    ∀ᶠ x in residual X, ∀ᶠ y in residual Y, P (x, y) := by
  classical
  obtain ⟨S, hSo, hSd, hSc, hS⟩ := mem_residual_iff.mp hP
  letI : Countable S := hSc.to_subtype
  have hAll : ∀ᶠ x in residual X, ∀ U : S, ∀ B : countableBasis Y,
      ∃ y ∈ (B : Set Y), (x, y) ∈ (U : Set (X × Y)) := by
    apply eventually_countable_forall.mpr
    intro U
    apply eventually_countable_forall.mpr
    intro B
    exact residual_of_dense_open
      (isOpen_exists_vertical (hSo U U.property)
        (isOpen_of_mem_countableBasis B.property))
      (dense_exists_vertical (hSd U U.property)
        (isOpen_of_mem_countableBasis B.property)
        (nonempty_of_mem_countableBasis B.property))
  filter_upwards [hAll] with x hx
  have hFiber (U : S) : {y : Y | (x, y) ∈ (U : Set (X × Y))} ∈ residual Y := by
    apply residual_of_dense_open
    · exact (hSo U U.property).preimage (continuous_const.prodMk continuous_id)
    · apply dense_iff_inter_open.mpr
      intro V hVo hVn
      obtain ⟨y, hyV⟩ := hVn
      obtain ⟨B, hB, _hyB, hBV⟩ :=
        (isBasis_countableBasis Y).exists_subset_of_mem_open hyV hVo
      obtain ⟨z, hzB, hzx⟩ := hx U ⟨B, hB⟩
      exact ⟨z, hBV hzB, hzx⟩
  have hAllFiber : ∀ᶠ y in residual Y, ∀ U : S, (x, y) ∈ (U : Set (X × Y)) :=
    eventually_countable_forall.mpr hFiber
  filter_upwards [hAllFiber] with y hy
  exact hS (by intro U hU; exact hy ⟨U, hU⟩)

/-- An immediate version with an actual section: a comeager set of pairs
has a comeager vertical section in a nonempty Baire first factor. -/
theorem exists_residual_section [BaireSpace X] [Nonempty X]
    [SecondCountableTopology Y] {P : X × Y → Prop}
    (hP : ∀ᶠ p in residual (X × Y), P p) :
    ∃ x, ∀ᶠ y in residual Y, P (x, y) :=
  (dense_of_mem_residual (eventually_residual_prod hP)).nonempty




end BenchmarkJump
end Source51
end BenchmarkJumpSubmission

/- Preserved source skeleton: CategoryLocal -/
namespace BenchmarkJumpSubmission
section Source52
open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A countable Baire cover of a nonempty open set has one member comeager
on a smaller nonempty open set. -/
theorem baire_cover_local_residual [BaireSpace X] {ι : Type*} [Countable ι]
    (A : ι → Set X) (hA : ∀ i, BaireMeasurableSet (A i))
    (Ω : Set X) (hΩ : IsOpen Ω) (hΩn : Ω.Nonempty)
    (hCover : Ω ⊆ ⋃ i, A i) :
    ∃ i, ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧ U ⊆ Ω ∧
      ∀ᶠ x in residual X, x ∈ U → x ∈ A i := by
  classical
  have hNon : ∃ i, ¬ IsMeagre (Ω ∩ A i) := by
    by_contra! h
    apply not_isMeagre_of_isOpen hΩ hΩn
    apply (isMeagre_iUnion h).mono
    intro x hxΩ
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hCover hxΩ)
    exact mem_iUnion.mpr ⟨i, hxΩ, hi⟩
  obtain ⟨i, hi⟩ := hNon
  obtain ⟨V, hVo, hEq⟩ := (hΩ.baireMeasurableSet.inter (hA i)).residualEq_isOpen
  have hEq' : ∀ᶠ x in residual X, x ∈ Ω ∩ A i ↔ x ∈ V :=
    Filter.eventuallyEq_set.mp hEq
  have hVn : V.Nonempty := by
    by_contra hn
    have hVe : V = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hi
    filter_upwards [hEq'] with x hx
    simpa [hVe] using hx
  obtain ⟨x, hxV, hxEq⟩ := (dense_of_mem_residual hEq').inter_open_nonempty V hVo hVn
  have hxΩ := ((hxEq.mpr hxV).1)
  refine ⟨i, V ∩ Ω, hVo.inter hΩ, ⟨x, hxV, hxΩ⟩, inter_subset_right, ?_⟩
  filter_upwards [hEq'] with y hy
  intro hyU
  exact (hy.mpr hyU.1).2

/-- Restricting an ambient comeager assertion to an open subspace preserves
comeagerness. -/
theorem eventually_residual_open_subspace (U : Set X) (hU : IsOpen U)
    {P : X → Prop} (hP : ∀ᶠ x in residual X, P x) :
    ∀ᶠ x : U in residual U, P (x : X) :=
  tendsto_residual_of_isOpenMap continuous_subtype_val hU.isOpenMap_subtype_val hP

/-- A residual assertion on an open subspace is the same as an ambient
residual implication on that open set. -/
theorem eventually_residual_of_open_subspace (U : Set X) (_hU : IsOpen U)
    {P : X → Prop} (hP : ∀ᶠ x : U in residual U, P (x : X)) :
    ∀ᶠ x in residual X, x ∈ U → P x := by
  classical
  have hm : IsMeagre {x : U | ¬ P (x : X)} := by
    simpa only [IsMeagre, compl_setOf, not_not] using hP
  have hImage : IsMeagre ((↑) '' {x : U | ¬ P (x : X)} : Set X) := hm.image_val
  filter_upwards [hImage] with x hx hxU
  by_contra hxP
  exact hx ⟨⟨x, hxU⟩, hxP, rfl⟩



end BenchmarkJump
end Source52
end BenchmarkJumpSubmission

/- Preserved source skeleton: OpenFiberSquare -/
namespace BenchmarkJumpSubmission
section Source53
open Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def OpenFiberSquare (s : X → Y) := {p : X × X | s p.1 = s p.2}

def fiberSquareLeft (s : X → Y) (z : OpenFiberSquare s) : X := z.1.1

def fiberSquareRight (s : X → Y) (z : OpenFiberSquare s) : X := z.1.2

theorem continuous_fiberSquareLeft (s : X → Y) : Continuous (fiberSquareLeft s) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_fiberSquareRight (s : X → Y) : Continuous (fiberSquareRight s) :=
  continuous_snd.comp continuous_subtype_val

theorem isOpenMap_fiberSquareLeft (s : X → Y) (hc : Continuous s) (ho : IsOpenMap s) :
    IsOpenMap (fiberSquareLeft s) := by
  intro W hW
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨z, hzW, rfl⟩
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hW
  have hzV : z.1 ∈ V := by
    change z ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hzW
  obtain ⟨A, B, hAo, hBo, hxA, hyB, hAB⟩ := isOpen_prod_iff.mp hVo z.1.1 z.1.2 hzV
  have hO : IsOpen (A ∩ s ⁻¹' (s '' B)) := hAo.inter ((ho B hBo).preimage hc)
  have hxO : fiberSquareLeft s z ∈ A ∩ s ⁻¹' (s '' B) :=
    ⟨hxA, ⟨z.1.2, hyB, z.property.symm⟩⟩
  apply mem_of_superset (hO.mem_nhds hxO)
  rintro x ⟨hxA, y, hyB, hys⟩
  refine ⟨⟨(x, y), hys.symm⟩, ?_, rfl⟩
  rw [← hVW]
  exact hAB ⟨hxA, hyB⟩

def fiberSquareSwapHomeomorph (s : X → Y) : OpenFiberSquare s ≃ₜ OpenFiberSquare s :=
  { toEquiv :=
      { toFun := fun z => ⟨(z.1.2, z.1.1), z.property.symm⟩
        invFun := fun z => ⟨(z.1.2, z.1.1), z.property.symm⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    continuous_toFun := ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _
    continuous_invFun := ((continuous_snd.comp continuous_subtype_val).prodMk
      (continuous_fst.comp continuous_subtype_val)).subtype_mk _ }

theorem isOpenMap_fiberSquareRight (s : X → Y) (hc : Continuous s) (ho : IsOpenMap s) :
    IsOpenMap (fiberSquareRight s) := by
  exact (isOpenMap_fiberSquareLeft s hc ho).comp (fiberSquareSwapHomeomorph s).isOpenMap





theorem isClosed_openFiberSquare [T2Space Y] (s : X → Y) (hc : Continuous s) :
    IsClosed {p : X × X | s p.1 = s p.2} :=
  isClosed_eq (hc.comp continuous_fst) (hc.comp continuous_snd)

theorem openFiberSquare_polish [PolishSpace X] [T2Space Y] (s : X → Y) (hc : Continuous s) :
    PolishSpace (OpenFiberSquare s) := (isClosed_openFiberSquare s hc).polishSpace

end BenchmarkJump
end
end Source53
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureRowCover -/
namespace BenchmarkJumpSubmission
section Source54
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump


local instance : PolishSpace PositiveDensityBundle := positiveDensityBundle_polish
local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩
local instance : MeasurableSpace PositiveDensityBundle := borel PositiveDensityBundle
local instance : BorelSpace PositiveDensityBundle := ⟨rfl⟩

def FullSupportMeasureEquivalence (μ ν : PositiveCylinderProbabilities) : Prop :=
  ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ∧
    ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)

theorem densityTarget_surjective : Function.Surjective densityTarget := by
  intro μ
  obtain ⟨z, hz⟩ := densitySource_surjective μ
  exact ⟨densityInverse z, (densityTarget_inverse z).trans hz⟩

/-- The concrete Baire cover of the genuine density bundle yields one fixed
row match, residually on a nonempty open subset over any prescribed target open set. -/
theorem measure_row_match_open
    (F : PositiveCylinderProbabilities → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism FullSupportMeasureEquivalence (Jump BoundedDifference) F)
    (k : ℕ) (A : Set PositiveCylinderProbabilities) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ l n : ℕ, ∃ W : Set PositiveDensityBundle,
      IsOpen W ∧ W.Nonempty ∧ W ⊆ densityTarget ⁻¹' A ∧
      ∀ᶠ z in residual PositiveDensityBundle,
        z ∈ W → UniformBound n (F (densityTarget z) k) (F (densitySource z) l) := by
  let B : ℕ × ℕ → Set PositiveDensityBundle := fun i =>
    {z | UniformBound i.2 (F (densityTarget z) k) (F (densitySource z) i.1)}
  have hB (i : ℕ × ℕ) : BaireMeasurableSet (B i) := by
    apply MeasurableSet.baireMeasurableSet
    exact (isClosed_uniformBound i.2).measurableSet.preimage
      (((measurable_pi_apply k).comp (hFm.comp continuous_densityTarget.measurable)).prodMk
        ((measurable_pi_apply i.1).comp (hFm.comp continuous_densitySource.measurable)))
  let Ω : Set PositiveDensityBundle := densityTarget ⁻¹' A
  have hΩo : IsOpen Ω := hAo.preimage continuous_densityTarget
  have hΩn : Ω.Nonempty := by
    obtain ⟨μ, hμ⟩ := hAn
    obtain ⟨z, hz⟩ := densityTarget_surjective μ
    refine ⟨z, ?_⟩
    change densityTarget z ∈ A
    rw [hz]
    exact hμ
  have hCover : Ω ⊆ ⋃ i, B i := by
    intro z _hz
    obtain ⟨l, hl⟩ := (hF (densitySource z) (densityTarget z)
      (densitySource_target_equivalent z)).2 k
    obtain ⟨n, hn⟩ := boundedDifference_equivalence.symm hl
    exact mem_iUnion.mpr ⟨(l, n), hn⟩
  obtain ⟨i, W, hWo, hWn, hWΩ, hWr⟩ :=
    baire_cover_local_residual B hB Ω hΩo hΩn hCover
  exact ⟨i.1, i.2, W, hWo, hWn, hWΩ, hWr⟩

theorem measure_good_fiber_pairs (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f g : PositiveCylinderProbabilities → RealSequences) (n : ℕ)
    (hRes : ∀ᶠ z in residual PositiveDensityBundle,
      z ∈ W → UniformBound n (f (densityTarget z)) (g (densitySource z))) :
    ∀ᶠ p in residual (OpenFiberSquare (fun z : W => densitySource z)),
      densityTarget p.1.1 ∈ D ∧ densityTarget p.1.2 ∈ D ∧
      UniformBound (2 * n) (f (densityTarget p.1.1)) (f (densityTarget p.1.2)) := by
  let s : W → PositiveCylinderProbabilities := fun z => densitySource z
  let t : W → PositiveCylinderProbabilities := fun z => densityTarget z
  have hsC : Continuous s := continuous_densitySource.comp continuous_subtype_val
  have hsO : IsOpenMap s := isOpenMap_densitySource.comp hWo.isOpenMap_subtype_val
  have htC : Continuous t := continuous_densityTarget.comp continuous_subtype_val
  have htO : IsOpenMap t := isOpenMap_densityTarget.comp hWo.isOpenMap_subtype_val
  have hResW : ∀ᶠ z : W in residual W, UniformBound n (f (t z)) (g (s z)) := by
    have h := eventually_residual_open_subspace W hWo hRes
    filter_upwards [h] with z hz
    exact hz z.property
  have h1 := tendsto_residual_of_isOpenMap (continuous_fiberSquareLeft s)
    (isOpenMap_fiberSquareLeft s hsC hsO) hResW
  have h2 := tendsto_residual_of_isOpenMap (continuous_fiberSquareRight s)
    (isOpenMap_fiberSquareRight s hsC hsO) hResW
  have hD1 := tendsto_residual_of_isOpenMap
    (htC.comp (continuous_fiberSquareLeft s))
    (htO.comp (isOpenMap_fiberSquareLeft s hsC hsO)) hD
  have hD2 := tendsto_residual_of_isOpenMap
    (htC.comp (continuous_fiberSquareRight s))
    (htO.comp (isOpenMap_fiberSquareRight s hsC hsO)) hD
  filter_upwards [h1, h2, hD1, hD2] with p hp1 hp2 hpD1 hpD2
  change UniformBound n (f (t (fiberSquareLeft s p))) (g (s (fiberSquareLeft s p))) at hp1
  change UniformBound n (f (t (fiberSquareRight s p))) (g (s (fiberSquareRight s p))) at hp2
  refine ⟨hpD1, hpD2, ?_⟩
  have heq : s (fiberSquareLeft s p) = s (fiberSquareRight s p) := p.property
  rw [← heq] at hp2
  have hB := uniformBound_trans hp1 (uniformBound_symm hp2)
  simpa only [two_mul] using hB




end BenchmarkJump
end
end Source54
end BenchmarkJumpSubmission

/- Preserved source skeleton: ContinuousSquareReweight -/
namespace BenchmarkJumpSubmission
section Source55
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def continuousSquareReweight (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) : PositiveCylinderProbabilities :=
  densityTarget (positiveContinuousSection w hw μ)

theorem continuous_continuousSquareReweight (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    Continuous (continuousSquareReweight w hw) :=
  continuous_densityTarget.comp (continuous_positiveContinuousSection w hw)

theorem densityVector_section_coe (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) :
    densityVector (positiveContinuousSection w hw μ) =ᵐ[
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)]
      fun x => ‖continuousDensityVector μ w‖⁻¹ * w x := by
  have hLift : densityVector (positiveContinuousSection w hw μ) = normalizedContinuousVector μ w :=
    (cantorRealHaarBasis μ).repr.symm_apply_apply _
  rw [hLift]
  filter_upwards [Lp.coeFn_smul ‖continuousDensityVector μ w‖⁻¹ (continuousDensityVector μ w),
    continuousDensityVector_coe μ w] with x hx hy
  simpa only [normalizedContinuousVector, Pi.smul_apply, smul_eq_mul, hy] using hx

theorem continuousSquareReweight_measure (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) :
    ((continuousSquareReweight w hw μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
        (fun x => ENNReal.ofReal ((‖continuousDensityVector μ w‖⁻¹ * w x) ^ 2)) := by
  apply withDensity_congr_ae
  filter_upwards [densityVector_section_coe w hw μ] with x hx
  rw [hx]

theorem continuousSquareReweight_inverse (w v : C(HaarCantor, ℝ))
    (hw : ∀ x, 0 < w x) (hv : ∀ x, 0 < v x) (hInv : ∀ x, w x * v x = 1)
    (μ : PositiveCylinderProbabilities) :
    continuousSquareReweight v hv (continuousSquareReweight w hw μ) = μ := by
  let ν := continuousSquareReweight w hw μ
  let A : ℝ := ‖continuousDensityVector μ w‖⁻¹
  let B : ℝ := ‖continuousDensityVector ν v‖⁻¹
  let c : ℝ := A ^ 2 * B ^ 2
  have hgw : Measurable (fun x => ENNReal.ofReal ((A * w x) ^ 2)) :=
    (measurable_const.mul w.continuous.measurable).pow_const 2 |>.ennreal_ofReal
  have hgv : Measurable (fun x => ENNReal.ofReal ((B * v x) ^ 2)) :=
    (measurable_const.mul v.continuous.measurable).pow_const 2 |>.ennreal_ofReal
  have hMeasure : ((continuousSquareReweight v hv ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      ENNReal.ofReal c • ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
    rw [continuousSquareReweight_measure v hv ν]
    have hν := congrArg (fun ρ : Measure HaarCantor =>
      ρ.withDensity (fun x => ENNReal.ofReal ((B * v x) ^ 2)))
        (continuousSquareReweight_measure w hw μ)
    change (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
      (fun x => ENNReal.ofReal ((B * v x) ^ 2))) = _
    refine hν.trans ?_
    change ((((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).withDensity
      (fun x => ENNReal.ofReal ((A * w x) ^ 2))).withDensity
      (fun x => ENNReal.ofReal ((B * v x) ^ 2))) = _
    rw [← withDensity_mul _ hgw hgv]
    have heq : (fun x => ENNReal.ofReal ((A * w x) ^ 2)) *
        (fun x => ENNReal.ofReal ((B * v x) ^ 2)) = fun _ => ENNReal.ofReal c := by
      funext x
      rw [Pi.mul_apply, ← ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      calc
        (A * w x) ^ 2 * (B * v x) ^ 2 = (A ^ 2 * B ^ 2) * (w x * v x) ^ 2 := by ring
        _ = c := by rw [hInv x]; simp only [one_pow, mul_one]; rfl
    rw [heq, withDensity_const]
  have hc : ENNReal.ofReal c = 1 := by
    have hm := congrArg (fun ρ : Measure HaarCantor => ρ univ) hMeasure
    simpa using hm.symm
  rw [hc, one_smul] at hMeasure
  apply Subtype.ext
  exact ProbabilityMeasure.toMeasure_injective hMeasure

def reciprocalContinuousMap (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) : C(HaarCantor, ℝ) :=
  ⟨fun x => (w x)⁻¹, w.continuous.inv₀ fun x => (hw x).ne'⟩

theorem reciprocalContinuousMap_positive (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    ∀ x, 0 < reciprocalContinuousMap w hw x := fun x => inv_pos.mpr (hw x)

def continuousSquareReweightHomeomorph (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    PositiveCylinderProbabilities ≃ₜ PositiveCylinderProbabilities :=
  { toEquiv :=
      { toFun := continuousSquareReweight w hw
        invFun := continuousSquareReweight (reciprocalContinuousMap w hw)
          (reciprocalContinuousMap_positive w hw)
        left_inv := continuousSquareReweight_inverse w (reciprocalContinuousMap w hw) hw
          (reciprocalContinuousMap_positive w hw) (fun x => mul_inv_cancel₀ (hw x).ne')
        right_inv := continuousSquareReweight_inverse (reciprocalContinuousMap w hw) w
          (reciprocalContinuousMap_positive w hw) hw (fun x => inv_mul_cancel₀ (hw x).ne') }
    continuous_toFun := continuous_continuousSquareReweight w hw
    continuous_invFun := continuous_continuousSquareReweight _ _ }



end BenchmarkJump
end
end Source55
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityBundleEndpoints -/
namespace BenchmarkJumpSubmission
section Source56
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def positiveDensityPointVector (ρ μ : PositiveCylinderProbabilities) :
    Lp ℝ 2 ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) :=
  MeasureEquivalenceHellinger.root
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)

theorem positiveDensityPointVector_positive (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    ∀ᵐ x ∂((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
      0 < positiveDensityPointVector ρ μ x := by
  letI : SigmaFinite ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := inferInstance
  letI : SigmaFinite ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := inferInstance
  filter_upwards [MeasureEquivalenceHellinger.root_coe
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
    hρμ.ae_le (Measure.rnDeriv_pos hμρ),
    Measure.rnDeriv_ne_top
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)] with x hx hp ht
  rw [show positiveDensityPointVector ρ μ x = _ from hx]
  exact Real.sqrt_pos.mpr (ENNReal.toReal_pos hp.ne' ht)

def positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) : PositiveDensityBundle :=
  ⟨(ρ, (cantorRealHaarBasis ρ).repr (positiveDensityPointVector ρ μ)), by
    constructor
    · change ∀ᵐ x ∂((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor),
        0 < haarLift ρ ((cantorRealHaarBasis ρ).repr (positiveDensityPointVector ρ μ)) x
      rw [haarLift, LinearIsometryEquiv.symm_apply_apply]
      exact positiveDensityPointVector_positive ρ μ hμρ hρμ
    · change ‖(cantorRealHaarBasis ρ).repr (positiveDensityPointVector ρ μ)‖ = 1
      rw [LinearIsometryEquiv.norm_map]
      exact MeasureEquivalenceHellinger.root_probability_norm _ _ hμρ⟩



@[simp] theorem densityVector_positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    densityVector (positiveDensityPoint ρ μ hμρ hρμ) = positiveDensityPointVector ρ μ :=
  (cantorRealHaarBasis ρ).repr.symm_apply_apply _

@[simp] theorem densityTarget_positiveDensityPoint (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    densityTarget (positiveDensityPoint ρ μ hμρ hρμ) = μ := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  change (MeasureEquivalenceDensity.squareMeasure
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (densityVector (positiveDensityPoint ρ μ hμρ hρμ)) : Measure HaarCantor) = _
  rw [densityVector_positiveDensityPoint]
  exact MeasureEquivalenceRNGraph.squareMeasure_root _ _ hμρ

theorem positiveDensityPoint_section_dist_sq (ρ μ : PositiveCylinderProbabilities)
    (hμρ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hρμ : ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) :
    dist (densityVector (positiveDensityPoint ρ μ hμρ hρμ)) (normalizedContinuousVector ρ w) ^ 2 =
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((continuousSquareReweight w hw ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  have hSec : densityVector (positiveContinuousSection w hw ρ) = normalizedContinuousVector ρ w :=
    (cantorRealHaarBasis ρ).repr.symm_apply_apply _
  rw [densityVector_positiveDensityPoint, ← hSec,
    ← root_densityTarget_eq (positiveContinuousSection w hw ρ)]
  exact MeasureEquivalenceHellinger.root_dist_sq _ _ _




end BenchmarkJump
end
end Source56
end BenchmarkJumpSubmission

/- Preserved source skeleton: DensityBundleTube -/
namespace BenchmarkJumpSubmission
section Source57
open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem densityBundle_section_hits_open (W : Set PositiveDensityBundle)
    (hWo : IsOpen W) (hWn : W.Nonempty) :
    ∃ μ : PositiveCylinderProbabilities, ∃ w : C(HaarCantor, ℝ),
      ∃ hw : ∀ x, 0 < w x, positiveContinuousSection w hw μ ∈ W := by
  obtain ⟨z, hzW⟩ := hWn
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hWo
  have hzV : z.1 ∈ V := by
    change z ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hzW
  obtain ⟨U, A, _hUo, hAo, hμU, haA, hUA⟩ := isOpen_prod_iff.mp hVo z.1.1 z.1.2 hzV
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hAo z.1.2 haA
  obtain ⟨w, hw, hNear⟩ := positiveContinuousSection_fiber_dense z ε hε
  refine ⟨densitySource z, w, hw, ?_⟩
  rw [← hVW]
  exact hUA ⟨hμU, hBall hNear⟩

/-- A genuine open bundle neighborhood contains a uniform L2 tube around
one positive continuous section over an open source neighborhood. -/
theorem densityBundle_tube_at_section (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (μ : PositiveCylinderProbabilities) (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (hSec : positiveContinuousSection w hw μ ∈ W) :
    ∃ U : Set PositiveCylinderProbabilities, ∃ ε : ℝ,
      IsOpen U ∧ μ ∈ U ∧ 0 < ε ∧
      ∀ z : PositiveDensityBundle, densitySource z ∈ U →
        dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W := by
  obtain ⟨V, hVo, hVW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hWo
  have hSecV : (μ, continuousSectionCoefficients w μ) ∈ V := by
    change positiveContinuousSection w hw μ ∈ Subtype.val ⁻¹' V
    rw [hVW]
    exact hSec
  obtain ⟨U₀, A, hU₀o, hAo, hμU₀, haA, hUA⟩ :=
    isOpen_prod_iff.mp hVo μ (continuousSectionCoefficients w μ) hSecV
  obtain ⟨δ, hδ, hBall⟩ := Metric.isOpen_iff.mp hAo (continuousSectionCoefficients w μ) haA
  let U := U₀ ∩ (continuousSectionCoefficients w) ⁻¹'
    Metric.ball (continuousSectionCoefficients w μ) (δ / 2)
  have hUo : IsOpen U := hU₀o.inter
    (Metric.isOpen_ball.preimage (continuous_continuousSectionCoefficients w hw))
  have hμU : μ ∈ U := ⟨hμU₀, by simp only [mem_preimage, Metric.mem_ball, dist_self]; positivity⟩
  refine ⟨U, δ / 2, hUo, hμU, by positivity, ?_⟩
  intro z hzU hzNear
  have hLift : haarLift (densitySource z)
      (continuousSectionCoefficients w (densitySource z)) =
      normalizedContinuousVector (densitySource z) w :=
    (cantorRealHaarBasis (densitySource z)).repr.symm_apply_apply _
  have hCoeff : dist z.1.2 (continuousSectionCoefficients w (densitySource z)) < δ / 2 := by
    rw [← dist_haarLift (densitySource z), hLift]
    exact hzNear
  have hSecNear : dist (continuousSectionCoefficients w (densitySource z))
      (continuousSectionCoefficients w μ) < δ / 2 := hzU.2
  have hNear : dist z.1.2 (continuousSectionCoefficients w μ) < δ := by
    have ht := dist_triangle z.1.2 (continuousSectionCoefficients w (densitySource z))
      (continuousSectionCoefficients w μ)
    linarith only [ht, hCoeff, hSecNear]
  rw [← hVW]
  exact hUA ⟨hzU.1, hBall hNear⟩



end BenchmarkJump
end
end Source57
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureRowClosure -/
namespace BenchmarkJumpSubmission
section Source58
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump




def measureFiberEndpoints (W : Set PositiveDensityBundle)
    (p : OpenFiberSquare (fun z : W => densitySource z)) :
    PositiveCylinderProbabilities × PositiveCylinderProbabilities :=
  (densityTarget p.1.1, densityTarget p.1.2)

theorem continuous_measureFiberEndpoints (W : Set PositiveDensityBundle) :
    Continuous (measureFiberEndpoints W) :=
  ((continuous_densityTarget.comp continuous_subtype_val).comp
    (continuous_fiberSquareLeft _)).prodMk
      ((continuous_densityTarget.comp continuous_subtype_val).comp (continuous_fiberSquareRight _))

theorem measure_uniformBound_of_mem_closure {D : Set PositiveCylinderProbabilities}
    (f : PositiveCylinderProbabilities → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ) (S : Set (PositiveCylinderProbabilities × PositiveCylinderProbabilities))
    (hSD : S ⊆ D ×ˢ D)
    (hBound : ∀ p ∈ S, UniformBound n (f p.1) (f p.2))
    (p : PositiveCylinderProbabilities × PositiveCylinderProbabilities) (hpD : p ∈ D ×ˢ D)
    (hp : p ∈ closure S) : UniformBound n (f p.1) (f p.2) := by
  have hc := ((hf p.1 hpD.1).prodMap (hf p.2 hpD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {q : RealSequences × RealSequences | UniformBound n q.1 q.2} := hBound
  have hcl := hc.mem_closure hp hm
  simpa only [(isClosed_uniformBound n).closure_eq] using hcl





end BenchmarkJump
end
end Source58
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityCoordinates -/
namespace BenchmarkJumpSubmission
section Source59
open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureUnitary

theorem isClopen_cantorCylinder (k : CantorCylinderIndex) : IsClopen (cantorCylinder k) := by
  change IsClopen ((fun x : HaarCantor => fun i : k.1 => x i) ⁻¹' k.2)
  exact (isClopen_discrete k.2).preimage (continuous_pi fun i => continuous_apply (i : ℕ))

def cantorProbabilityCoordinates (μ : ProbabilityMeasure HaarCantor) : CantorCylinderIndex → ℝ :=
  fun k => (μ : Measure HaarCantor).real (cantorCylinder k)

theorem continuous_cantorProbabilityCoordinates : Continuous cantorProbabilityCoordinates :=
  continuous_pi (fun k => continuous_clopen_mass _ (isClopen_cantorCylinder k))

theorem injective_cantorProbabilityCoordinates : Function.Injective cantorProbabilityCoordinates := by
  intro μ ν h
  apply Subtype.ext
  change (μ : Measure HaarCantor) = (ν : Measure HaarCantor)
  apply ext_of_generate_finite (range cantorCylinder) cantorCylinder_generates.symm cantorCylinder_isPiSystem
  · rintro s ⟨k,rfl⟩
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ : Measure HaarCantor) _)
      (measure_ne_top (ν : Measure HaarCantor) _)).mp
    exact congrFun h k
  · simp

theorem isEmbedding_cantorProbabilityCoordinates : IsEmbedding cantorProbabilityCoordinates :=
  continuous_cantorProbabilityCoordinates.isClosedEmbedding injective_cantorProbabilityCoordinates |>.isEmbedding

/-- The weak topology on Cantor probabilities is exactly the topology of all finite-cylinder masses. -/
theorem continuous_cantorProbability_iff {X : Type*} [TopologicalSpace X]
    (f : X → ProbabilityMeasure HaarCantor) :
    Continuous f ↔ ∀ k : CantorCylinderIndex,
      Continuous (fun x => (f x : Measure HaarCantor).real (cantorCylinder k)) := by
  rw [isEmbedding_cantorProbabilityCoordinates.continuous_iff, continuous_pi_iff]
  rfl

theorem tendsto_cantorProbability_iff {I : Type*} {L : Filter I}
    (f : I → ProbabilityMeasure HaarCantor) (μ : ProbabilityMeasure HaarCantor) :
    Tendsto f L (𝓝 μ) ↔ ∀ k : CantorCylinderIndex,
      Tendsto (fun i => (f i : Measure HaarCantor).real (cantorCylinder k)) L
        (𝓝 ((μ : Measure HaarCantor).real (cantorCylinder k))) := by
  rw [isEmbedding_cantorProbabilityCoordinates.tendsto_nhds_iff, tendsto_pi_nhds]
  rfl

theorem cantorProbability_finite_coordinate_neighborhood (μ : ProbabilityMeasure HaarCantor)
    {U : Set (ProbabilityMeasure HaarCantor)} (hU : U ∈ 𝓝 μ) :
    ∃ (I : Finset CantorCylinderIndex) (V : CantorCylinderIndex → Set ℝ),
      (∀ k, V k ∈ 𝓝 (cantorProbabilityCoordinates μ k)) ∧
      ∀ ν : ProbabilityMeasure HaarCantor,
        (∀ k ∈ I, cantorProbabilityCoordinates ν k ∈ V k) → ν ∈ U := by
  classical
  rw [isEmbedding_cantorProbabilityCoordinates.isInducing.nhds_eq_comap μ] at hU
  obtain ⟨W,hW,hWU⟩ := Filter.mem_comap.mp hU
  rw [nhds_pi,Filter.mem_pi'] at hW
  obtain ⟨I,V,hV,hVW⟩ := hW
  refine ⟨I,V,hV,fun ν hν => hWU (hVW ?_)⟩
  exact fun k hk => hν k hk

end BenchmarkJump
end
end Source59
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityMix -/
namespace BenchmarkJumpSubmission
section Source60
open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def cantorProbabilityMix (t : unitInterval) (μ ν : ProbabilityMeasure HaarCantor) : ProbabilityMeasure HaarCantor :=
  ⟨ENNReal.ofReal (1 - (t : ℝ)) • (μ : Measure HaarCantor) +
    ENNReal.ofReal (t : ℝ) • (ν : Measure HaarCantor), ⟨by
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr t.property.2) t.property.1]
      norm_num⟩⟩

theorem cantorProbabilityMix_apply (t : unitInterval) (μ ν : ProbabilityMeasure HaarCantor) (A : Set HaarCantor) :
    (cantorProbabilityMix t μ ν : Measure HaarCantor) A =
      ENNReal.ofReal (1 - (t : ℝ)) * (μ : Measure HaarCantor) A +
        ENNReal.ofReal (t : ℝ) * (ν : Measure HaarCantor) A := rfl

theorem cantorProbabilityMix_real (t : unitInterval) (μ ν : ProbabilityMeasure HaarCantor) (A : Set HaarCantor) :
    (cantorProbabilityMix t μ ν : Measure HaarCantor).real A =
      (1 - (t : ℝ)) * (μ : Measure HaarCantor).real A +
        (t : ℝ) * (ν : Measure HaarCantor).real A := by
  change (ENNReal.ofReal (1 - (t : ℝ)) • (μ : Measure HaarCantor) +
    ENNReal.ofReal (t : ℝ) • (ν : Measure HaarCantor)).real A = _
  rw [measureReal_add_apply
    (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
    (by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (sub_nonneg.mpr t.property.2),
    ENNReal.toReal_ofReal t.property.1]

theorem cantorProbabilityMix_self (t : unitInterval) (μ : ProbabilityMeasure HaarCantor) :
    cantorProbabilityMix t μ μ = μ := by
  apply injective_cantorProbabilityCoordinates
  funext k
  change (cantorProbabilityMix t μ μ : Measure HaarCantor).real _ = (μ : Measure HaarCantor).real _
  rw [cantorProbabilityMix_real]
  ring

theorem continuous_cantorProbabilityMix :
    Continuous (fun p : unitInterval × (ProbabilityMeasure HaarCantor × ProbabilityMeasure HaarCantor) =>
      cantorProbabilityMix p.1 p.2.1 p.2.2) := by
  apply (continuous_cantorProbability_iff _).mpr
  intro k
  simp_rw [cantorProbabilityMix_real]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((continuous_clopen_mass _ (isClopen_cantorCylinder k)).comp (continuous_fst.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_clopen_mass _ (isClopen_cantorCylinder k)).comp (continuous_snd.comp continuous_snd)))

theorem cantorProbabilityMix_fullSupport_right (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ : ProbabilityMeasure HaarCantor) (ν : PositiveCylinderProbabilities) :
    cantorProbabilityMix t μ ν ∈ PositiveCylinderProbabilities := by
  intro n s
  rw [cantorProbabilityMix_real]
  have hnonneg : 0 ≤ (1 - (t : ℝ)) * (μ : Measure HaarCantor).real (prefixCylinder s) :=
    mul_nonneg (sub_nonneg.mpr t.property.2) measureReal_nonneg
  exact add_pos_of_nonneg_of_pos hnonneg (mul_pos ht (ν.property n s))

def fullSupportMix (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ : ProbabilityMeasure HaarCantor) (ν : PositiveCylinderProbabilities) : PositiveCylinderProbabilities :=
  ⟨cantorProbabilityMix t μ ν, cantorProbabilityMix_fullSupport_right t ht μ ν⟩

theorem continuous_fullSupportMix (t : unitInterval) (ht : 0 < (t : ℝ)) :
    Continuous (fun p : ProbabilityMeasure HaarCantor × PositiveCylinderProbabilities =>
      fullSupportMix t ht p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_cantorProbabilityMix.comp
    (continuous_const.prodMk (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

end BenchmarkJump
end
end Source60
end BenchmarkJumpSubmission

/- Preserved source skeleton: HellingerMidpoint -/
namespace BenchmarkJumpSubmission
section Source61
/-! Concrete Hellinger midpoint estimates for the measure-jump proof. -/

open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem sqrt_midpoint_square_bound (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt ((a + b) / 2)) ^ 2 ≤
      (1 / 2 : ℝ) * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  have hz := Real.sq_sqrt (show 0 ≤ (a + b) / 2 by positivity)
  have hs : (Real.sqrt a + Real.sqrt b) ^ 2 ≤
      (2 * Real.sqrt ((a + b) / 2)) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
  have hlinear : Real.sqrt a + Real.sqrt b ≤ 2 * Real.sqrt ((a + b) / 2) :=
    (sq_le_sq₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (by positivity)).mp hs
  have hmul := mul_le_mul_of_nonneg_left hlinear (Real.sqrt_nonneg a)
  nlinarith

theorem integrable_hellinger_energy {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x =>
      (Real.sqrt (μ.rnDeriv ρ x).toReal - Real.sqrt (ν.rnDeriv ρ x).toReal) ^ 2) ρ := by
  have hmem := (MeasureEquivalenceHellinger.sqrt_rnDeriv_memLp μ ρ).sub
    (MeasureEquivalenceHellinger.sqrt_rnDeriv_memLp ν ρ)
  exact (memLp_two_iff_integrable_sq
    (((Measure.measurable_rnDeriv μ ρ).ennreal_toReal.sqrt.sub
      (Measure.measurable_rnDeriv ν ρ).ennreal_toReal.sqrt).aestronglyMeasurable)).mp hmem

def measureMidpoint {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : Measure α :=
  (1 / 2 : ℝ≥0) • (μ + ν)

/-- The actual midpoint measure contracts squared Hellinger distance to
either endpoint by a factor of at least one half, with a common reference. -/
theorem hellinger_energy_midpoint {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ] :
    MeasureEquivalenceHellinger.energy μ (measureMidpoint μ ν) ρ ≤
      (1 / 2 : ℝ) * MeasureEquivalenceHellinger.energy μ ν ρ := by
  letI : IsFiniteMeasure (measureMidpoint μ ν) := by
    unfold measureMidpoint
    infer_instance
  have hRN : ∀ᵐ x ∂ρ,
      ((measureMidpoint μ ν).rnDeriv ρ x).toReal =
        ((μ.rnDeriv ρ x).toReal + (ν.rnDeriv ρ x).toReal) / 2 := by
    filter_upwards [Measure.rnDeriv_smul_left (μ + ν) ρ (1 / 2 : ℝ≥0),
      Measure.rnDeriv_add μ ν ρ, Measure.rnDeriv_ne_top μ ρ, Measure.rnDeriv_ne_top ν ρ]
      with x hs ha hμ hν
    change ((measureMidpoint μ ν).rnDeriv ρ x) =
      (1 / 2 : ℝ≥0) • (μ + ν).rnDeriv ρ x at hs
    rw [hs, ha]
    simp only [Pi.add_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_add hμ hν]
    norm_num
    ring
  unfold MeasureEquivalenceHellinger.energy
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_hellinger_energy μ (measureMidpoint μ ν) ρ)
    ((integrable_hellinger_energy μ ν ρ).const_mul (1 / 2 : ℝ))
  filter_upwards [hRN] with x hx
  rw [hx]
  exact sqrt_midpoint_square_bound _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg



end BenchmarkJump
end
end Source61
end BenchmarkJumpSubmission

/- Preserved source skeleton: HellingerConvexEstimates -/
namespace BenchmarkJumpSubmission
section Source62
open MeasureTheory Filter Set
open scoped ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem sqrt_difference_square_le_abs (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg a)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) (Real.sqrt_nonneg b)
    nlinarith

theorem sqrt_convex_smoothing_square_bound (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Real.sqrt ((1 - t) * a + t * b) - Real.sqrt b) ^ 2 ≤
      (1 - t) * (Real.sqrt a - Real.sqrt b) ^ 2 := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hmix : 0 ≤ (1 - t) * a + t * b :=
    add_nonneg (mul_nonneg (by linarith) ha) (mul_nonneg ht0 hb)
  have hsz := Real.sq_sqrt hmix
  have hvar : 0 ≤ t * (1 - t) * (Real.sqrt a - Real.sqrt b) ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  have hsq : ((1 - t) * Real.sqrt a + t * Real.sqrt b) ^ 2 ≤
      (Real.sqrt ((1 - t) * a + t * b)) ^ 2 := by nlinarith
  have hlin : (1 - t) * Real.sqrt a + t * Real.sqrt b ≤
      Real.sqrt ((1 - t) * a + t * b) :=
    (sq_le_sq₀ (add_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _))
      (mul_nonneg ht0 (Real.sqrt_nonneg _))) (Real.sqrt_nonneg _)).mp hsq
  have hm := mul_le_mul_of_nonneg_left hlin (Real.sqrt_nonneg b)
  nlinarith

def measureBlend {α : Type*} [MeasurableSpace α] (t : ℝ≥0)
    (μ ν : Measure α) : Measure α := (1 - t) • μ + t • ν

instance measureBlend_isFiniteMeasure {α : Type*} [MeasurableSpace α] (t : ℝ≥0)
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (measureBlend t μ ν) := by unfold measureBlend; infer_instance

theorem measureBlend_rnDeriv {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (t : ℝ≥0) (ht : t ≤ 1) :
    ∀ᵐ x ∂ρ, ((measureBlend t μ ν).rnDeriv ρ x).toReal =
      (1 - (t : ℝ)) * (μ.rnDeriv ρ x).toReal + (t : ℝ) * (ν.rnDeriv ρ x).toReal := by
  filter_upwards [Measure.rnDeriv_add ((1 - t) • μ) (t • ν) ρ,
    Measure.rnDeriv_smul_left μ ρ (1 - t), Measure.rnDeriv_smul_left ν ρ t,
    Measure.rnDeriv_ne_top ((1 - t) • μ) ρ, Measure.rnDeriv_ne_top (t • ν) ρ]
    with x ha hμ hν htμ htν
  change (((((1 - t) • μ) + t • ν).rnDeriv ρ x)).toReal = _
  rw [ha]
  simp only [Pi.add_apply, ENNReal.toReal_add htμ htν]
  rw [hμ, hν]
  simp only [Pi.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, NNReal.coe_sub ht, NNReal.coe_one]

theorem hellinger_energy_smoothing {α : Type*} [MeasurableSpace α]
    (μ ν ρ : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite ρ]
    (t : ℝ≥0) (ht : t ≤ 1) :
    MeasureEquivalenceHellinger.energy (measureBlend t μ ν) ν ρ ≤
      (1 - (t : ℝ)) * MeasureEquivalenceHellinger.energy μ ν ρ := by
  unfold MeasureEquivalenceHellinger.energy
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_hellinger_energy (measureBlend t μ ν) ν ρ)
    ((integrable_hellinger_energy μ ν ρ).const_mul _)
  filter_upwards [measureBlend_rnDeriv μ ν ρ t ht] with x hx
  rw [hx]
  exact sqrt_convex_smoothing_square_bound _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    t.property (NNReal.coe_le_coe.mpr ht)

theorem integrable_toReal_rnDeriv_finite {α : Type*} [MeasurableSpace α]
    (μ ρ : Measure α) [IsFiniteMeasure μ] : Integrable (fun x => (μ.rnDeriv ρ x).toReal) ρ := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    Measure.integrableOn_toReal_rnDeriv (ν := ρ) (measure_ne_top μ univ)

/-- Along the actual convex segment between arbitrary probability measures,
squared Hellinger distance is at most twice the difference of parameters. -/
theorem hellinger_energy_blend_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (t u : ℝ≥0) (ht : t ≤ 1) (hu : u ≤ 1) :
    MeasureEquivalenceHellinger.energy (measureBlend t μ ν) (measureBlend u μ ν) (μ + ν) ≤
      2 * |(t : ℝ) - (u : ℝ)| := by
  have hIμ := integrable_toReal_rnDeriv_finite μ (μ + ν)
  have hIν := integrable_toReal_rnDeriv_finite ν (μ + ν)
  have hμac : μ ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right ν
  have hνac : ν ≪ μ + ν := Measure.AbsolutelyContinuous.rfl.add_right' μ
  have hI := (hIμ.add hIν).const_mul |(t : ℝ) - (u : ℝ)|
  have hBound : MeasureEquivalenceHellinger.energy (measureBlend t μ ν) (measureBlend u μ ν) (μ + ν) ≤
      ∫ x, |(t : ℝ) - (u : ℝ)| *
        ((μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν) := by
    apply integral_mono_ae (integrable_hellinger_energy _ _ _) hI
    filter_upwards [measureBlend_rnDeriv μ ν (μ + ν) t ht,
      measureBlend_rnDeriv μ ν (μ + ν) u hu] with x htx hux
    calc
      _ ≤ |((measureBlend t μ ν).rnDeriv (μ + ν) x).toReal -
          ((measureBlend u μ ν).rnDeriv (μ + ν) x).toReal| :=
        sqrt_difference_square_le_abs _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      _ = |(t : ℝ) - (u : ℝ)| *
          |(ν.rnDeriv (μ + ν) x).toReal - (μ.rnDeriv (μ + ν) x).toReal| := by
        rw [htx, hux, ← abs_mul]
        congr 1
        ring
      _ ≤ |(t : ℝ) - (u : ℝ)| *
          ((μ.rnDeriv (μ + ν) x).toReal + (ν.rnDeriv (μ + ν) x).toReal) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith only [
          (ENNReal.toReal_nonneg : 0 ≤ (μ.rnDeriv (μ + ν) x).toReal),
          (ENNReal.toReal_nonneg : 0 ≤ (ν.rnDeriv (μ + ν) x).toReal)]
  calc
    _ ≤ _ := hBound
    _ = |(t : ℝ) - (u : ℝ)| * (μ.real univ + ν.real univ) := by
      rw [integral_const_mul, integral_add hIμ hIν,
        Measure.integral_toReal_rnDeriv hμac, Measure.integral_toReal_rnDeriv hνac]
    _ = _ := by simp only [measureReal_def, measure_univ, ENNReal.toReal_one]; ring




end BenchmarkJump
end
end Source62
end BenchmarkJumpSubmission

/- Preserved source skeleton: PositiveProbabilityMix -/
namespace BenchmarkJumpSubmission
section Source63
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def positiveProbabilityMix (t : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    PositiveCylinderProbabilities :=
  ⟨cantorProbabilityMix t μ ν, by
    by_cases ht : 0 < (t : ℝ)
    · exact cantorProbabilityMix_fullSupport_right t ht μ ν
    · have ht0 : (t : ℝ) = 0 := le_antisymm (not_lt.mp ht) t.property.1
      intro n s
      rw [cantorProbabilityMix_real, ht0]
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using μ.property n s⟩

theorem continuous_positiveProbabilityMix :
    Continuous (fun p : unitInterval × (PositiveCylinderProbabilities × PositiveCylinderProbabilities) =>
      positiveProbabilityMix p.1 p.2.1 p.2.2) := by
  apply Continuous.subtype_mk
  exact continuous_cantorProbabilityMix.comp
    (continuous_fst.prodMk ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))



theorem positiveProbabilityMix_measure (t : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureBlend (⟨(t : ℝ), t.property.1⟩ : ℝ≥0)
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  let r : ℝ≥0 := ⟨(t : ℝ), t.property.1⟩
  have hr : r ≤ 1 := t.property.2
  have hA : ((1 - r : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (1 - (t : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_sub hr, NNReal.coe_one]
    rfl
  have hB : (r : ℝ≥0∞) = ENNReal.ofReal (t : ℝ) := ENNReal.ofReal_coe_nnreal.symm
  change ENNReal.ofReal (1 - (t : ℝ)) • (μ : ProbabilityMeasure HaarCantor).toMeasure +
      ENNReal.ofReal (t : ℝ) • (ν : ProbabilityMeasure HaarCantor).toMeasure =
    (1 - r) • (μ : ProbabilityMeasure HaarCantor).toMeasure +
      r • (ν : ProbabilityMeasure HaarCantor).toMeasure
  ext A hAm
  simp only [Measure.add_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hA, hB]

theorem positiveProbabilityMix_ac (t : unitInterval) (μ ν ρ : PositiveCylinderProbabilities)
    (hμ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hν : ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  intro A hA
  change (cantorProbabilityMix t μ ν : Measure HaarCantor) A = 0
  rw [cantorProbabilityMix_apply, hμ hA, hν hA, mul_zero, mul_zero, add_zero]

theorem right_ac_positiveProbabilityMix (t : unitInterval) (ht : 0 < (t : ℝ))
    (μ ν : PositiveCylinderProbabilities) :
    ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  intro A hA
  change ENNReal.ofReal (1 - (t : ℝ)) *
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A + ENNReal.ofReal (t : ℝ) *
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = 0 at hA
  exact (mul_eq_zero.mp (add_eq_zero.mp hA).2).resolve_left (ENNReal.ofReal_pos.mpr ht).ne'




end BenchmarkJump
end
end Source63
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureHellingerFiberLift -/
namespace BenchmarkJumpSubmission
section Source64
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

def halfUnitInterval : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem positiveProbabilityMix_half_measure (μ ν : PositiveCylinderProbabilities) :
    ((positiveProbabilityMix halfUnitInterval μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
  ext A hA
  change ENNReal.ofReal (1 - (halfUnitInterval : ℝ)) *
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A +
      ENNReal.ofReal (halfUnitInterval : ℝ) *
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = _
  simp only [measureMidpoint, Measure.smul_apply, Measure.add_apply, ENNReal.smul_def,
    smul_eq_mul, halfUnitInterval]
  norm_num
  rw [mul_add]
  norm_num [ENNReal.ofReal_div_of_pos]





end BenchmarkJump
end
end Source64
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureSmoothingFiberLift -/
namespace BenchmarkJumpSubmission
section Source65
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem hellinger_energy_nonneg {α : Type*} [MeasurableSpace α] (μ ν ρ : Measure α) :
    0 ≤ MeasureEquivalenceHellinger.energy μ ν ρ := integral_nonneg fun _ => sq_nonneg _

theorem measure_endpoint_lift_of_energy
    (W : Set PositiveDensityBundle) (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (μ σ ρ : PositiveCylinderProbabilities) (hRew : continuousSquareReweight w hw ρ = σ)
    (hρU : ρ ∈ U) (hμρ : FullSupportMeasureEquivalence μ ρ)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) < ε ^ 2) :
    ∃ z : W, densitySource z = ρ ∧ densityTarget z = μ := by
  let z := positiveDensityPoint ρ μ hμρ.1 hμρ.2
  have hSq := positiveDensityPoint_section_dist_sq ρ μ hμρ.1 hμρ.2 w hw
  rw [hRew] at hSq
  have hNear : dist (densityVector z) (normalizedContinuousVector ρ w) < ε :=
    (sq_lt_sq₀ dist_nonneg hε.le).mp (hSq.trans_lt hE)
  exact ⟨⟨z, hTube z hρU hNear⟩, rfl, densityTarget_positiveDensityPoint ρ μ hμρ.1 hμρ.2⟩

/-- Smoothing arbitrary endpoints by a positive amount of their midpoint
produces actual same-source bundle points inside the prescribed L2 tube. -/
theorem measure_smoothing_fiber_lift
    (W : Set PositiveDensityBundle) (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (μ₁ μ₂ σ ρ : PositiveCylinderProbabilities)
    (hσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hRew : continuousSquareReweight w hw ρ = σ) (hρU : ρ ∈ U)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2)
    (r : unitInterval) (hr : 0 < (r : ℝ)) :
    ∃ p : OpenFiberSquare (fun z : W => densitySource z),
      measureFiberEndpoints W p = (positiveProbabilityMix r μ₁ σ, positiveProbabilityMix r μ₂ σ) := by
  let κ : Measure HaarCantor := ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  have hκ₁ : ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ :=
    Measure.AbsolutelyContinuous.rfl.add_right _
  have hκ₂ : ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ :=
    Measure.AbsolutelyContinuous.rfl.add_right' _
  have hκσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ := by
    intro A hA
    rw [hσ]
    change ((1 / 2 : ℝ≥0) • κ) A = 0
    rw [Measure.smul_apply, hA, smul_zero]
  have hσκ : κ ≪ ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
    intro A hA
    rw [hσ] at hA
    change ((1 / 2 : ℝ≥0) • κ) A = 0 at hA
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hA
    exact (mul_eq_zero.mp hA).resolve_left (by norm_num)
  have hρσ := densitySource_target_equivalent (positiveContinuousSection w hw ρ)
  change FullSupportMeasureEquivalence ρ (continuousSquareReweight w hw ρ) at hρσ
  rw [hRew] at hρσ
  have hMid₁ := hellinger_energy_midpoint
    ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
  rw [← hσ] at hMid₁
  have hσswap : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) := by
    rw [hσ, measureMidpoint, measureMidpoint, add_comm]
  have hMid₂ := hellinger_energy_midpoint
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
  rw [← hσswap, MeasureEquivalenceHellinger.energy_symm
    ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ] at hMid₂
  have hLift (μ : PositiveCylinderProbabilities)
      (hμκ : ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪ κ)
      (hMid : MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ ≤
        (1 / 2 : ℝ) * MeasureEquivalenceHellinger.energy
          ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ) :
      ∃ z : W, densitySource z = ρ ∧ densityTarget z = positiveProbabilityMix r μ σ := by
    let η := positiveProbabilityMix r μ σ
    have hησ := positiveProbabilityMix_ac r μ σ σ (hμκ.trans hσκ) Measure.AbsolutelyContinuous.rfl
    have hση := right_ac_positiveProbabilityMix r hr μ σ
    have hηρ := hησ.trans hρσ.2
    have hρη := hρσ.1.trans hση
    have hηκ := hησ.trans hκσ
    have hSmooth := hellinger_energy_smoothing
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
        (⟨(r : ℝ), r.property.1⟩ : ℝ≥0) r.property.2
    rw [← positiveProbabilityMix_measure r μ σ] at hSmooth
    have hNonneg := hellinger_energy_nonneg
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ
    have hContract : (1 - (r : ℝ)) * MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ ≤
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ := by
      nlinarith only [r.property.1, hNonneg]
    have hReference := MeasureEquivalenceHellinger.energy_reference_independent
      ((η : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) κ hηρ hρσ.2 hηκ hκσ
    have hESmall : MeasureEquivalenceHellinger.energy
        ((η : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) < ε ^ 2 := by
      rw [hReference]
      exact lt_of_le_of_lt (hSmooth.trans (hContract.trans hMid))
        (by have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε; nlinarith only [hE, hεsq])
    exact measure_endpoint_lift_of_energy W U w hw ε hε hTube η σ ρ hRew hρU ⟨hηρ, hρη⟩ hESmall
  obtain ⟨z₁, hs₁, ht₁⟩ := hLift μ₁ hκ₁ hMid₁
  obtain ⟨z₂, hs₂, ht₂⟩ := hLift μ₂ hκ₂ hMid₂
  exact ⟨⟨(z₁, z₂), hs₁.trans hs₂.symm⟩, Prod.ext ht₁ ht₂⟩



end BenchmarkJump
end
end Source65
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureSmallPairBound -/
namespace BenchmarkJumpSubmission
section Source66
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump


local instance : PolishSpace PositiveDensityBundle := positiveDensityBundle_polish

theorem positiveProbabilityMix_zero (μ ν : PositiveCylinderProbabilities) :
    positiveProbabilityMix 0 μ ν = μ := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  change ENNReal.ofReal (1 - ((0 : unitInterval) : ℝ)) *
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A +
      ENNReal.ofReal ((0 : unitInterval) : ℝ) *
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = _
  simp

def smoothingParameter (N : ℕ) : unitInterval :=
  ⟨1 / ((N : ℝ) + 1), by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith only [Nat.cast_nonneg (α := ℝ) N]⟩

theorem smoothingParameter_pos (N : ℕ) : 0 < (smoothingParameter N : ℝ) := by
  dsimp [smoothingParameter]
  positivity

theorem tendsto_smoothingParameter : Tendsto smoothingParameter atTop (𝓝 0) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_smoothing (μ σ : PositiveCylinderProbabilities) :
    Tendsto (fun N => positiveProbabilityMix (smoothingParameter N) μ σ) atTop (𝓝 μ) := by
  have hArg : Continuous (fun r : unitInterval => (r, (μ, σ))) :=
    continuous_id.prodMk continuous_const
  have hc := continuous_positiveProbabilityMix.comp hArg
  change Continuous (fun r : unitInterval => positiveProbabilityMix r μ σ) at hc
  simpa only [positiveProbabilityMix_zero] using (hc.tendsto 0).comp tendsto_smoothingParameter

/-- Arbitrary Hellinger-close endpoints in the continuity set obey the same
closed output bound: smoothing gives actual fiber points, and good fiber
points are dense. No intersection with a fixed Hellinger ball is assumed. -/
theorem measure_small_pair_bound
    (W : Set PositiveDensityBundle) (hWo : IsOpen W)
    (U : Set PositiveCylinderProbabilities)
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x) (ε : ℝ) (hε : 0 < ε)
    (hTube : ∀ z : PositiveDensityBundle, densitySource z ∈ U →
      dist (densityVector z) (normalizedContinuousVector (densitySource z) w) < ε → z ∈ W)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f g : PositiveCylinderProbabilities → RealSequences) (hf : ContinuousOn f D) (n : ℕ)
    (hRes : ∀ᶠ z in residual PositiveDensityBundle,
      z ∈ W → UniformBound n (f (densityTarget z)) (g (densitySource z)))
    (μ₁ μ₂ σ ρ : PositiveCylinderProbabilities)
    (hσ : ((σ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) =
      measureMidpoint ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (hRew : continuousSquareReweight w hw ρ = σ) (hρU : ρ ∈ U)
    (hE : MeasureEquivalenceHellinger.energy
      ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2)
    (hμ₁D : μ₁ ∈ D) (hμ₂D : μ₂ ∈ D) : UniformBound (2 * n) (f μ₁) (f μ₂) := by
  letI : PolishSpace W := hWo.polishSpace
  letI : PolishSpace (OpenFiberSquare (fun z : W => densitySource z)) :=
    openFiberSquare_polish _ (continuous_densitySource.comp continuous_subtype_val)
  let G : Set (OpenFiberSquare (fun z : W => densitySource z)) :=
    {q | densityTarget q.1.1 ∈ D ∧ densityTarget q.1.2 ∈ D ∧
      UniformBound (2 * n) (f (densityTarget q.1.1)) (f (densityTarget q.1.2))}
  let S := measureFiberEndpoints W '' G
  have hG : G ∈ residual _ := measure_good_fiber_pairs W hWo D hD f g n hRes
  have hDense (p : OpenFiberSquare (fun z : W => densitySource z)) :
      measureFiberEndpoints W p ∈ closure S :=
    (continuous_measureFiberEndpoints W).continuousAt.continuousWithinAt.mem_closure_image
      (dense_of_mem_residual hG p)
  have hSmooth (N : ℕ) :
      (positiveProbabilityMix (smoothingParameter N) μ₁ σ,
        positiveProbabilityMix (smoothingParameter N) μ₂ σ) ∈ closure S := by
    obtain ⟨p, hp⟩ := measure_smoothing_fiber_lift W U w hw ε hε hTube
      μ₁ μ₂ σ ρ hσ hRew hρU hE (smoothingParameter N) (smoothingParameter_pos N)
    exact hp ▸ hDense p
  have hLim := (tendsto_smoothing μ₁ σ).prodMk_nhds (tendsto_smoothing μ₂ σ)
  have hp : (μ₁, μ₂) ∈ closure S := isClosed_closure.mem_of_tendsto hLim
    (Eventually.of_forall hSmooth)
  apply measure_uniformBound_of_mem_closure f hf (2 * n) S _ _ (μ₁, μ₂) ⟨hμ₁D, hμ₂D⟩ hp
  · rintro q ⟨r, hr, rfl⟩
    exact ⟨hr.1, hr.2.1⟩
  · rintro q ⟨r, hr, rfl⟩
    exact hr.2.2



end BenchmarkJump
end
end Source66
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorConvexNeighborhoods -/
namespace BenchmarkJumpSubmission
section Source67
open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem cantorProbability_convex_neighborhood (μ : ProbabilityMeasure HaarCantor)
    {U : Set (ProbabilityMeasure HaarCantor)} (hU : U ∈ 𝓝 μ) :
    ∃ V : Set (ProbabilityMeasure HaarCantor), IsOpen V ∧ μ ∈ V ∧ V ⊆ U ∧
      ∀ t : unitInterval, ∀ ν ∈ V, ∀ ρ ∈ V, cantorProbabilityMix t ν ρ ∈ V := by
  classical
  obtain ⟨I,W,hW,hWU⟩ := cantorProbability_finite_coordinate_neighborhood μ hU
  choose ε hε hεW using fun k => Metric.mem_nhds_iff.mp (hW k)
  let V : Set (ProbabilityMeasure HaarCantor) :=
    ⋂ k ∈ I, cantorProbabilityCoordinates ⁻¹' {x | x k ∈ Metric.ball (cantorProbabilityCoordinates μ k) (ε k)}
  have hVo : IsOpen V := by
    apply isOpen_biInter_finset
    intro k _hk
    exact Metric.isOpen_ball.preimage ((continuous_apply k).comp continuous_cantorProbabilityCoordinates)
  have hmem (ν : ProbabilityMeasure HaarCantor) : ν ∈ V ↔
      ∀ k ∈ I, cantorProbabilityCoordinates ν k ∈ Metric.ball (cantorProbabilityCoordinates μ k) (ε k) := by
    simp [V]
  refine ⟨V,hVo,(hmem μ).mpr (fun k _ => Metric.mem_ball_self (hε k)), ?_, ?_⟩
  · intro ν hν
    apply hWU
    intro k hk
    exact hεW k ((hmem ν).mp hν k hk)
  · intro t ν hν ρ hρ
    apply (hmem _).mpr
    intro k hk
    change (cantorProbabilityMix t ν ρ : Measure HaarCantor).real (MeasureUnitary.cantorCylinder k) ∈ _
    rw [cantorProbabilityMix_real]
    exact (convex_ball (cantorProbabilityCoordinates μ k) (ε k))
      ((hmem ν).mp hν k hk) ((hmem ρ).mp hρ k hk)
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

end BenchmarkJump
end
end Source67
end BenchmarkJumpSubmission

/- Preserved source skeleton: PositiveConvexNeighborhoods -/
namespace BenchmarkJumpSubmission
section Source68
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

def PositiveMixConvex (O : Set PositiveCylinderProbabilities) : Prop :=
  ∀ t : unitInterval, ∀ μ ∈ O, ∀ ν ∈ O, positiveProbabilityMix t μ ν ∈ O

theorem positiveProbability_convex_neighborhood (μ : PositiveCylinderProbabilities)
    {U : Set PositiveCylinderProbabilities} (hU : U ∈ 𝓝 μ) :
    ∃ O : Set PositiveCylinderProbabilities,
      IsOpen O ∧ μ ∈ O ∧ O ⊆ U ∧ PositiveMixConvex O := by
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap μ] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  obtain ⟨C, hCo, hμC, hCV, hC⟩ := cantorProbability_convex_neighborhood
    (μ : ProbabilityMeasure HaarCantor) hV
  refine ⟨Subtype.val ⁻¹' C, hCo.preimage continuous_subtype_val, hμC,
    fun ν hν => hVU (hCV hν), ?_⟩
  intro t ν hν ρ hρ
  exact hC t ν hν ρ hρ



end BenchmarkJump
end
end Source68
end BenchmarkJumpSubmission

/- Preserved source skeleton: PositiveReweightNeighborhood -/
namespace BenchmarkJumpSubmission
section Source69
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem continuousSquareReweightHomeomorph_apply (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (μ : PositiveCylinderProbabilities) :
    continuousSquareReweightHomeomorph w hw μ = continuousSquareReweight w hw μ := rfl

theorem homeomorph_positive_convex_neighborhood
    (H : PositiveCylinderProbabilities ≃ₜ PositiveCylinderProbabilities)
    (U A : Set PositiveCylinderProbabilities) (hUo : IsOpen U) (hAo : IsOpen A)
    (μ₀ : PositiveCylinderProbabilities) (hμ₀U : μ₀ ∈ U) (hHμ₀A : H μ₀ ∈ A) :
    ∃ O : Set PositiveCylinderProbabilities,
      IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧ PositiveMixConvex O ∧
      ∀ σ ∈ O, ∃ ρ ∈ U, H ρ = σ := by
  let N : Set PositiveCylinderProbabilities := A ∩ H.symm ⁻¹' U
  have hNo : IsOpen N := hAo.inter (hUo.preimage H.symm.continuous)
  have hHμ₀N : H μ₀ ∈ N := by
    refine ⟨hHμ₀A, ?_⟩
    change H.symm (H μ₀) ∈ U
    simpa only [H.symm_apply_apply] using hμ₀U
  obtain ⟨O, hOo, hHO, hON, hConvex⟩ :=
    positiveProbability_convex_neighborhood (H μ₀) (hNo.mem_nhds hHμ₀N)
  refine ⟨O, hOo, ⟨H μ₀, hHO⟩, fun σ hσ => (hON hσ).1, hConvex, ?_⟩
  intro σ hσ
  exact ⟨H.symm σ, (hON hσ).2, H.apply_symm_apply σ⟩

theorem positiveReweight_convex_neighborhood
    (w : C(HaarCantor, ℝ)) (hw : ∀ x, 0 < w x)
    (U A : Set PositiveCylinderProbabilities) (hUo : IsOpen U) (hAo : IsOpen A)
    (μ₀ : PositiveCylinderProbabilities) (hμ₀U : μ₀ ∈ U)
    (hHμ₀A : continuousSquareReweight w hw μ₀ ∈ A) :
    ∃ O : Set PositiveCylinderProbabilities,
      IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧ PositiveMixConvex O ∧
      ∀ σ ∈ O, ∃ ρ ∈ U, continuousSquareReweight w hw ρ = σ := by
  have h := homeomorph_positive_convex_neighborhood (continuousSquareReweightHomeomorph w hw)
    U A hUo hAo μ₀ hμ₀U (by rwa [continuousSquareReweightHomeomorph_apply])
  simpa only [continuousSquareReweightHomeomorph_apply] using h



end BenchmarkJump
end
end Source69
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureLocalSmallRows -/
namespace BenchmarkJumpSubmission
section Source70
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish

local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩



/- Every Borel jump homomorphism on the genuine full-support measure space
has a uniform small-Hellinger row bound on a nonempty convex weak-open set. -/
theorem measure_local_small_rows
    (F : PositiveCylinderProbabilities → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism FullSupportMeasureEquivalence (Jump BoundedDifference) F)
    (k : ℕ) (A : Set PositiveCylinderProbabilities) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ O D : Set PositiveCylinderProbabilities, ∃ ε : ℝ, ∃ n : ℕ,
      IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧ PositiveMixConvex O ∧ 0 < ε ∧
      D ∈ residual PositiveCylinderProbabilities ∧ ContinuousOn (fun μ => F μ k) D ∧
      ∀ μ₁ ∈ O, ∀ μ₂ ∈ O, μ₁ ∈ D → μ₂ ∈ D →
        MeasureEquivalenceHellinger.energy
          ((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
          (((μ₁ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
            ((μ₂ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2 →
        UniformBound n (F μ₁ k) (F μ₂ k) := by
  obtain ⟨l, n, W, hWo, hWn, hWA, hRes⟩ := measure_row_match_open F hFm hF k A hAo hAn
  obtain ⟨μ₀, w, hw, hSec⟩ := densityBundle_section_hits_open W hWo hWn
  obtain ⟨U, ε, hUo, hμ₀U, hε, hTube⟩ := densityBundle_tube_at_section W hWo μ₀ w hw hSec
  have hν₀A : continuousSquareReweight w hw μ₀ ∈ A := by
    change densityTarget (positiveContinuousSection w hw μ₀) ∈ A
    exact hWA hSec
  obtain ⟨O, hOo, hOn, hOA, hOconvex, hLift⟩ :=
    positiveReweight_convex_neighborhood w hw U A hUo hAo μ₀ hμ₀U hν₀A
  let f : PositiveCylinderProbabilities → RealSequences := fun μ => F μ k
  let g : PositiveCylinderProbabilities → RealSequences := fun μ => F μ l
  obtain ⟨D, hDG, hDd, hf⟩ := measurable_continuousOn_residual f ((measurable_pi_apply k).comp hFm)
  have hD : D ∈ residual PositiveCylinderProbabilities := residual_of_dense_Gδ hDG hDd
  refine ⟨O, D, ε, 2 * n, hOo, hOn, hOA,
    hOconvex, hε, hD, hf, ?_⟩
  intro μ₁ hμ₁O μ₂ hμ₂O hμ₁D hμ₂D hE
  let σ := positiveProbabilityMix halfUnitInterval μ₁ μ₂
  have hσO : σ ∈ O := hOconvex halfUnitInterval μ₁ hμ₁O μ₂ hμ₂O
  obtain ⟨ρ, hρU, hRew⟩ := hLift σ hσO
  exact measure_small_pair_bound W hWo U w hw ε hε hTube D hD f g hf n hRes
    μ₁ μ₂ σ ρ (positiveProbabilityMix_half_measure μ₁ μ₂) hRew hρU hE hμ₁D hμ₂D



end BenchmarkJump
end
end Source70
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleReduction -/
namespace BenchmarkJumpSubmission
section Source71
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









































































end MeasureEquivalenceCircleReduction
end
end Source71
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleCategory -/
namespace BenchmarkJumpSubmission
section Source72
/-! The concrete category properties of null difference on the compact
product of circles. These are the source-side category hypotheses of the
first jump obstruction, proved here without assuming the obstruction. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

























end BenchmarkJump
end Source72
end BenchmarkJumpSubmission

/- Preserved source skeleton: FiniteFourier -/
namespace BenchmarkJumpSubmission
section Source73
/-!
Finite Hilbert-valued Fourier identities for the finite-torus feasibility check.
This file is a separate development and does not alter the earlier checks.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceFourier

variable {G E : Type*} [AddCommGroup G] [Fintype G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

















end MeasureEquivalenceFourier
end Source73
end BenchmarkJumpSubmission

/- Preserved source skeleton: ScalarMultiplier -/
namespace BenchmarkJumpSubmission
section Source74
/-!
# Scalar finite-product estimate

This file verifies only an elementary scalar estimate used in a Fourier argument.
It does not formalize Parseval's identity, the trigonometric multiplier bound,
or any theorem about Borel reducibility or equivalence of measures.
-/

open scoped BigOperators

namespace MeasureEquivalenceScalar









end MeasureEquivalenceScalar
end Source74
end BenchmarkJumpSubmission

/- Preserved source skeleton: TrigMultiplier -/
namespace BenchmarkJumpSubmission
section Source75
/-!
# Trigonometric coordinate multiplier

This file checks the real-variable estimate used for each nonzero Fourier
coordinate.  In particular it applies to integer frequencies, without assuming
integrality.  It does not formalize the Fourier expansion or Parseval's identity.
-/

namespace MeasureEquivalenceTrig







end MeasureEquivalenceTrig
end Source75
end BenchmarkJumpSubmission

/- Preserved source skeleton: FiniteTorus -/
namespace BenchmarkJumpSubmission
section Source76
/-!
Finite product tori: arbitrary single-coordinate shifts compared with the
uniform three-point product walk. This is stronger than the half-turn case.
-/

open scoped BigOperators ComplexConjugate

namespace MeasureEquivalenceTorus

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]















































end MeasureEquivalenceTorus
end Source76
end BenchmarkJumpSubmission

/- Preserved source skeleton: GridObstruction -/
namespace BenchmarkJumpSubmission
section Source77
/-! The dimension-uniform contradiction, including the two continuity
quantifiers. Actual circle-sequence grids are instantiated in a separate file. -/

open Filter Topology
open scoped Topology BigOperators

namespace MeasureEquivalenceGrid

open MeasureEquivalenceTorus

variable {H E : Type*} [NormedAddCommGroup H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]







end MeasureEquivalenceGrid
end Source77
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleGrids -/
namespace BenchmarkJumpSubmission
section Source78
open Filter Topology
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircle

open MeasureEquivalenceTorus MeasureEquivalenceGrid



variable (p : ℝ≥0∞) {m n : ℕ} [NeZero m]













































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]





end MeasureEquivalenceCircle
end
end Source78
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleTopology -/
namespace BenchmarkJumpSubmission
section Source79
open Filter Topology Set TopologicalSpace
open scoped Topology BigOperators ENNReal NNReal

noncomputable section

namespace MeasureEquivalenceCircleTopology

open MeasureEquivalenceCircle



variable (p : ℝ≥0∞) [Fact (1 ≤ p)]



































end MeasureEquivalenceCircleTopology
end
end Source79
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleRowCover -/
namespace BenchmarkJumpSubmission
section Source80
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology



























end BenchmarkJump
end
end Source80
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleSmallPairs -/
namespace BenchmarkJumpSubmission
section Source81
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology






































end BenchmarkJump
end
end Source81
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleRowClosure -/
namespace BenchmarkJumpSubmission
section Source82
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology








end BenchmarkJump
end
end Source82
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleChart -/
namespace BenchmarkJumpSubmission
section Source83
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump





























end BenchmarkJump
end
end Source83
end BenchmarkJumpSubmission

/- Preserved source skeleton: IntervalInterpolation -/
namespace BenchmarkJumpSubmission
section Source84
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump
































end BenchmarkJump
end
end Source84
end BenchmarkJumpSubmission

/- Preserved source skeleton: ChartConvexNeighborhood -/
namespace BenchmarkJumpSubmission
section Source85
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump




















end BenchmarkJump
end
end Source85
end BenchmarkJumpSubmission

/- Preserved source skeleton: CircleChartConstancy -/
namespace BenchmarkJumpSubmission
section Source86
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump



theorem boundedDifference_fin_chain (m : ℕ) (u : Fin (m + 1) → RealSequences)
    (hStep : ∀ j : Fin m, BoundedDifference (u j.castSucc) (u j.succ)) :
    BoundedDifference (u 0) (u (Fin.last m)) := by
  have hAux : ∀ j : ℕ, ∀ hj : j ≤ m,
      BoundedDifference (u 0) (u ⟨j, Nat.lt_succ_of_le hj⟩) := by
    intro j
    induction j with
    | zero =>
        intro _hj
        exact boundedDifference_equivalence.refl _
    | succ j ih =>
        intro hj
        have hjm : j < m := by omega
        exact boundedDifference_equivalence.trans (ih (by omega)) (hStep ⟨j, hjm⟩)
  exact hAux m le_rfl

def chainParameter (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) : ℝ := (j : ℝ) / m

theorem chainParameter_nonneg (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) :
    0 ≤ chainParameter m hm j := by unfold chainParameter; positivity

theorem chainParameter_le_one (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) :
    chainParameter m hm j ≤ 1 := by
  unfold chainParameter
  apply (div_le_one (by exact_mod_cast hm)).mpr
  exact_mod_cast Nat.le_of_lt_succ j.isLt

theorem chainParameter_step (m : ℕ) (hm : 0 < m) (j : Fin m) :
    |chainParameter m hm j.castSucc - chainParameter m hm j.succ| = 1 / (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have heq : chainParameter m hm j.castSucc - chainParameter m hm j.succ = -(1 / (m : ℝ)) := by
    unfold chainParameter
    simp only [Fin.coe_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]



end BenchmarkJump
end
end Source86
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureInterpolationEnergy -/
namespace BenchmarkJumpSubmission
section Source87
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

namespace BenchmarkJump

theorem positiveProbabilityMix_one (μ ν : PositiveCylinderProbabilities) :
    positiveProbabilityMix 1 μ ν = ν := by
  apply Subtype.ext
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  change ENNReal.ofReal (1 - ((1 : unitInterval) : ℝ)) *
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A +
      ENNReal.ofReal ((1 : unitInterval) : ℝ) *
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = _
  simp

theorem positiveProbabilityMix_ac_sum (t : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
      (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) := by
  intro A hA
  have hZero := add_eq_zero.mp hA
  change ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = 0 ∧
    ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A = 0 at hZero
  change (cantorProbabilityMix t μ ν : Measure HaarCantor) A = 0
  rw [cantorProbabilityMix_apply, hZero.1, hZero.2, mul_zero, mul_zero, add_zero]

theorem positiveProbabilityMix_energy_le (t u : unitInterval) (μ ν : PositiveCylinderProbabilities) :
    MeasureEquivalenceHellinger.energy
      ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) ≤
      2 * |(t : ℝ) - (u : ℝ)| := by
  have hReference := MeasureEquivalenceHellinger.energy_reference_independent
    ((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    (((positiveProbabilityMix t μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
      ((positiveProbabilityMix u μ ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor))
    (Measure.AbsolutelyContinuous.rfl.add_right _) (Measure.AbsolutelyContinuous.rfl.add_right' _)
    (positiveProbabilityMix_ac_sum t μ ν) (positiveProbabilityMix_ac_sum u μ ν)
  rw [hReference, positiveProbabilityMix_measure, positiveProbabilityMix_measure]
  exact hellinger_energy_blend_le _ _ _ _ t.property.2 u.property.2

def positiveChainParameter (m : ℕ) (hm : 0 < m) (j : Fin (m + 1)) : unitInterval :=
  ⟨chainParameter m hm j, chainParameter_nonneg m hm j, chainParameter_le_one m hm j⟩

theorem positiveChainParameter_zero (m : ℕ) (hm : 0 < m) : positiveChainParameter m hm 0 = 0 := by
  apply Subtype.ext
  simp only [positiveChainParameter, chainParameter, Fin.val_zero, Nat.cast_zero, zero_div]
  rfl

theorem positiveChainParameter_last (m : ℕ) (hm : 0 < m) :
    positiveChainParameter m hm (Fin.last m) = 1 := by
  apply Subtype.ext
  simp only [positiveChainParameter, chainParameter, Fin.val_last,
    div_self (show (m : ℝ) ≠ 0 by exact_mod_cast hm.ne')]
  rfl

theorem positiveProbabilityMix_chain_step_energy (m : ℕ) (hm : 0 < m) (j : Fin m)
    (μ ν : PositiveCylinderProbabilities) :
    let a := positiveProbabilityMix (positiveChainParameter m hm j.castSucc) μ ν
    let b := positiveProbabilityMix (positiveChainParameter m hm j.succ) μ ν
    MeasureEquivalenceHellinger.energy
      ((a : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      ((b : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (((a : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
        ((b : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) ≤ 2 / (m : ℝ) := by
  have h := positiveProbabilityMix_energy_le (positiveChainParameter m hm j.castSucc)
    (positiveChainParameter m hm j.succ) μ ν
  change _ ≤ 2 * |chainParameter m hm j.castSucc - chainParameter m hm j.succ| at h
  rw [chainParameter_step m hm j] at h
  simpa only [mul_one_div] using h




end BenchmarkJump
end
end Source87
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureInterpolationChain -/
namespace BenchmarkJumpSubmission
section Source88
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish

def positiveMixOn (O : Set PositiveCylinderProbabilities) (hO : PositiveMixConvex O)
    (t : unitInterval) (p : O × O) : O :=
  ⟨positiveProbabilityMix t p.1 p.2, hO t p.1 p.1.property p.2 p.2.property⟩

theorem continuous_positiveMixOn (O : Set PositiveCylinderProbabilities) (hO : PositiveMixConvex O)
    (t : unitInterval) : Continuous (positiveMixOn O hO t) := by
  have hArg : Continuous (fun p : O × O =>
      (t, ((p.1 : PositiveCylinderProbabilities), (p.2 : PositiveCylinderProbabilities)))) :=
    continuous_const.prodMk ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  exact (continuous_positiveProbabilityMix.comp hArg).subtype_mk _

theorem isOpenMap_positiveMixOn (O : Set PositiveCylinderProbabilities) (hOo : IsOpen O)
    (hO : PositiveMixConvex O) (t : unitInterval)
    (hOpen : IsOpenMap (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
      positiveProbabilityMix t p.1 p.2)) : IsOpenMap (positiveMixOn O hO t) :=
  (hOpen.comp (hOo.isOpenMap_subtype_val.prodMap hOo.isOpenMap_subtype_val)).subtype_mk _

/-- The exact finite-chain category step, with the separately checked global
affine-mixture openness theorem supplied explicitly at this interface. -/
theorem measure_interpolation_generic_pairs
    (hOpen : ∀ t : unitInterval, IsOpenMap
      (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
        positiveProbabilityMix t p.1 p.2))
    (O : Set PositiveCylinderProbabilities) (hOo : IsOpen O) (hO : PositiveMixConvex O)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f : PositiveCylinderProbabilities → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ μ ∈ O, ∀ ν ∈ O, μ ∈ D → ν ∈ D →
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2 →
      BoundedDifference (f μ) (f ν)) :
    ∀ᶠ p : O × O in residual (O × O), BoundedDifference (f p.1) (f p.2) := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (show 0 < ε ^ 2 / 2 by positivity)
  let m : ℕ := M + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hdiv : 2 / (m : ℝ) < ε ^ 2 := by
    have h : 1 / (m : ℝ) < ε ^ 2 / 2 := by exact_mod_cast hM
    have heq : 2 / (m : ℝ) = 2 * (1 / (m : ℝ)) := by ring
    rw [heq]
    linarith only [h]
  let P (j : Fin (m + 1)) : O × O → O := positiveMixOn O hO (positiveChainParameter m hm j)
  have hDO : ∀ᶠ x : O in residual O, (x : PositiveCylinderProbabilities) ∈ D :=
    eventually_residual_open_subspace O hOo hD
  have hAll : ∀ᶠ p : O × O in residual (O × O),
      ∀ j : Fin (m + 1), (P j p : PositiveCylinderProbabilities) ∈ D := by
    apply eventually_countable_forall.mpr
    intro j
    exact tendsto_residual_of_isOpenMap (continuous_positiveMixOn O hO _)
      (isOpenMap_positiveMixOn O hOo hO _ (hOpen _)) hDO
  filter_upwards [hAll] with p hp
  let u : Fin (m + 1) → RealSequences := fun j => f (P j p)
  have hStep (j : Fin m) : BoundedDifference (u j.castSucc) (u j.succ) := by
    apply hSmall (P j.castSucc p) (P j.castSucc p).property
      (P j.succ p) (P j.succ p).property (hp j.castSucc) (hp j.succ)
    exact (positiveProbabilityMix_chain_step_energy m hm j p.1 p.2).trans_lt hdiv
  have hP0 : P 0 p = p.1 := by
    apply Subtype.ext
    change positiveProbabilityMix (positiveChainParameter m hm 0) p.1 p.2 = p.1
    rw [positiveChainParameter_zero, positiveProbabilityMix_zero]
  have hP1 : P (Fin.last m) p = p.2 := by
    apply Subtype.ext
    change positiveProbabilityMix (positiveChainParameter m hm (Fin.last m)) p.1 p.2 = p.2
    rw [positiveChainParameter_last, positiveProbabilityMix_one]
  have hChain := boundedDifference_fin_chain m u hStep
  change BoundedDifference (f (P 0 p)) (f (P (Fin.last m) p)) at hChain
  rwa [hP0, hP1] at hChain

theorem measure_interpolation_constant_on_open
    (hOpen : ∀ t : unitInterval, IsOpenMap
      (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
        positiveProbabilityMix t p.1 p.2))
    (O : Set PositiveCylinderProbabilities) (hOo : IsOpen O) (hOn : O.Nonempty)
    (hO : PositiveMixConvex O)
    (D : Set PositiveCylinderProbabilities) (hD : D ∈ residual PositiveCylinderProbabilities)
    (f : PositiveCylinderProbabilities → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ μ ∈ O, ∀ ν ∈ O, μ ∈ D → ν ∈ D →
      MeasureEquivalenceHellinger.energy
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
        (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) +
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) < ε ^ 2 →
      BoundedDifference (f μ) (f ν)) :
    ∃ a : RealSequences, ∀ᶠ μ in residual PositiveCylinderProbabilities,
      μ ∈ O → BoundedDifference (f μ) a := by
  letI : Nonempty O := hOn.to_subtype
  letI : PolishSpace O := hOo.polishSpace
  have hPair := measure_interpolation_generic_pairs hOpen O hOo hO D hD f ε hε hSmall
  obtain ⟨μ, hμ⟩ := exists_residual_section hPair
  refine ⟨f μ, eventually_residual_of_open_subspace O hOo ?_⟩
  filter_upwards [hμ] with ν hν
  exact boundedDifference_equivalence.symm hν



end BenchmarkJump
end
end Source88
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorSmallCylinders -/
namespace BenchmarkJumpSubmission
section Source89
open MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

namespace BenchmarkJump

def lowerMassChild (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) : Bool := by
  classical
  exact if (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s false)) ≤
      (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s true)) then false else true

theorem prefixCylinder_mass_split (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) :
    (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s false)) +
      (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s true)) =
      (μ : Measure HaarCantor).real (prefixCylinder s) := by
  rw [← measureReal_union (prefixCylinder_children_disjoint s) (isClopen_prefixCylinder _).isClosed.measurableSet,
    prefixCylinder_split]

theorem lowerMassChild_bound (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) :
    (μ : Measure HaarCantor).real (prefixCylinder (Fin.snoc s (lowerMassChild μ s))) ≤
      (μ : Measure HaarCantor).real (prefixCylinder s) / 2 := by
  classical
  have hs := prefixCylinder_mass_split μ s
  unfold lowerMassChild
  split_ifs with h
  · linarith
  · linarith

def smallMassPrefix (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) :
    (m : ℕ) → Fin (n + m) → Bool
  | 0 => s
  | m + 1 => Fin.snoc (smallMassPrefix μ s m) (lowerMassChild μ (smallMassPrefix μ s m))

theorem smallMassPrefix_subset (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) (m : ℕ) :
    prefixCylinder (smallMassPrefix μ s m) ⊆ prefixCylinder s := by
  induction m with
  | zero => exact Subset.rfl
  | succ m ih =>
    intro x hx
    apply ih
    exact ((mem_prefixCylinder_snoc _ _ x).mp hx).1

theorem smallMassPrefix_bound (μ : ProbabilityMeasure HaarCantor) {n : ℕ} (s : Fin n → Bool) (m : ℕ) :
    (μ : Measure HaarCantor).real (prefixCylinder (smallMassPrefix μ s m)) ≤
      (1 / 2 : ℝ) ^ m * (μ : Measure HaarCantor).real (prefixCylinder s) := by
  induction m with
  | zero => simp [smallMassPrefix]
  | succ m ih =>
    have hc := lowerMassChild_bound μ (smallMassPrefix μ s m)
    change (μ : Measure HaarCantor).real
      (prefixCylinder (Fin.snoc (smallMassPrefix μ s m) (lowerMassChild μ (smallMassPrefix μ s m)))) ≤ _
    rw [pow_succ]
    nlinarith

end BenchmarkJump
end
end Source89
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorPrefixPerturbation -/
namespace BenchmarkJumpSubmission
section Source90
open MeasureTheory Set Filter Topology
open scoped Topology

noncomputable section

namespace BenchmarkJump

def prefixPoint {n : ℕ} (s : Fin n → Bool) : HaarCantor :=
  fun i => if hi : i < n then s ⟨i,hi⟩ else false

theorem prefixPoint_mem {n : ℕ} (s : Fin n → Bool) : prefixPoint s ∈ prefixCylinder s := by
  intro i
  simp [prefixPoint,i.isLt]

def prefixRedirect (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) (x : HaarCantor) : HaarCantor :=
  prefixPoint (smallMassPrefix μ (fun i : Fin n => x i) m)

theorem continuous_prefixRedirect (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    Continuous (prefixRedirect μ n m) := by
  exact (continuous_of_discreteTopology (f := fun s : Fin n → Bool => prefixPoint (smallMassPrefix μ s m))).comp
    (continuous_pi fun i : Fin n => continuous_apply (i : ℕ))

theorem prefixRedirect_eq (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) (x : HaarCantor)
    (i : ℕ) (hi : i < n) : prefixRedirect μ n m x i = x i := by
  exact (smallMassPrefix_subset μ (fun j : Fin n => x j) m
    (prefixPoint_mem (smallMassPrefix μ (fun j : Fin n => x j) m))) ⟨i,hi⟩

theorem prefixCylinder_pairwise_disjoint (n : ℕ) :
    Pairwise (fun (s t : Fin n → Bool) => Disjoint (prefixCylinder s) (prefixCylinder t)) := by
  intro s t hst
  apply disjoint_left.mpr
  intro x hs ht
  apply hst
  funext i
  exact (hs i).symm.trans (ht i)

theorem prefixCylinder_iUnion (n : ℕ) : (⋃ s : Fin n → Bool, prefixCylinder s) = univ := by
  apply eq_univ_of_forall
  intro x
  exact mem_iUnion.mpr ⟨fun i => x i, fun _ => rfl⟩

theorem prefixCylinder_mass_sum (μ : ProbabilityMeasure HaarCantor) (n : ℕ) :
    ∑ s : Fin n → Bool, (μ : Measure HaarCantor).real (prefixCylinder s) = 1 := by
  rw [← measureReal_iUnion_fintype (prefixCylinder_pairwise_disjoint n)
    (fun s => (isClopen_prefixCylinder s).isClosed.measurableSet), prefixCylinder_iUnion]
  simp

def smallPrefixRegion (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) : Set HaarCantor :=
  ⋃ s : Fin n → Bool, prefixCylinder (smallMassPrefix μ s m)

theorem smallPrefixRegion_clopen (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    IsClopen (smallPrefixRegion μ n m) :=
  isClopen_iUnion_of_finite (fun s => isClopen_prefixCylinder (smallMassPrefix μ s m))

theorem smallPrefixRegion_mass_bound (μ : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    (μ : Measure HaarCantor).real (smallPrefixRegion μ n m) ≤ (1 / 2 : ℝ) ^ m := by
  calc
    _ ≤ ∑ s : Fin n → Bool, (μ : Measure HaarCantor).real (prefixCylinder (smallMassPrefix μ s m)) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ s : Fin n → Bool, (1 / 2 : ℝ) ^ m * (μ : Measure HaarCantor).real (prefixCylinder s) :=
      Finset.sum_le_sum (fun s _ => smallMassPrefix_bound μ s m)
    _ = _ := by rw [← Finset.mul_sum, prefixCylinder_mass_sum, mul_one]

theorem prefixRedirect_mem_smallPrefixRegion (μ : ProbabilityMeasure HaarCantor)
    (n m : ℕ) (x : HaarCantor) : prefixRedirect μ n m x ∈ smallPrefixRegion μ n m :=
  mem_iUnion.mpr ⟨fun i : Fin n => x i, prefixPoint_mem _⟩

def redirectedProbability (μ ν : ProbabilityMeasure HaarCantor) (n m : ℕ) : ProbabilityMeasure HaarCantor :=
  ⟨(ν : Measure HaarCantor).map (prefixRedirect μ n m),
    Measure.isProbabilityMeasure_map (continuous_prefixRedirect μ n m).measurable.aemeasurable⟩

theorem redirectedProbability_cylinder (μ ν : ProbabilityMeasure HaarCantor)
    (n m : ℕ) (k : MeasureUnitary.CantorCylinderIndex) (hk : ∀ i ∈ k.1, i < n) :
    (redirectedProbability μ ν n m : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) =
      (ν : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) := by
  rw [show (redirectedProbability μ ν n m : Measure HaarCantor) =
    (ν : Measure HaarCantor).map (prefixRedirect μ n m) from rfl,
    Measure.map_apply (continuous_prefixRedirect μ n m).measurable (MeasureUnitary.cantorCylinder_measurable k)]
  congr 1
  ext x
  change ((fun i : k.1 => prefixRedirect μ n m x i) ∈ k.2) ↔ ((fun i : k.1 => x i) ∈ k.2)
  have he : (fun i : k.1 => prefixRedirect μ n m x i) = (fun i : k.1 => x i) := by
    funext i
    exact prefixRedirect_eq μ n m x i (hk i i.property)
  rw [he]

theorem redirectedProbability_tendsto (μ ν : ProbabilityMeasure HaarCantor) (m : ℕ) :
    Tendsto (fun n => redirectedProbability μ ν n m) atTop (𝓝 ν) := by
  apply (tendsto_cantorProbability_iff _ _).mpr
  intro k
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (k.1.sup id)] with n hn
  apply congrArg ENNReal.toReal
  exact (redirectedProbability_cylinder μ ν n m k (fun i hi =>
    (Finset.le_sup (f := id) hi).trans_lt hn)).symm

end BenchmarkJump
end
end Source90
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorCylinderRefinement -/
namespace BenchmarkJumpSubmission
section Source91
open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BenchmarkJump

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open MeasureUnitary

theorem cantorCylinder_constant_on_prefix (k : CantorCylinderIndex) (n : ℕ)
    (hk : ∀ i ∈ k.1, i < n) (s : Fin n → Bool) (x : HaarCantor) (hx : x ∈ prefixCylinder s) :
    x ∈ cantorCylinder k ↔ prefixPoint s ∈ cantorCylinder k := by
  have he : (fun i : k.1 => x i) = (fun i : k.1 => prefixPoint s i) := by
    funext i
    exact (hx ⟨i,hk i i.property⟩).trans ((prefixPoint_mem s) ⟨i,hk i i.property⟩).symm
  change ((fun i : k.1 => x i) ∈ k.2) ↔ ((fun i : k.1 => prefixPoint s i) ∈ k.2)
  rw [he]

theorem cantorCylinder_inter_prefix (k : CantorCylinderIndex) (n : ℕ)
    (hk : ∀ i ∈ k.1, i < n) (s : Fin n → Bool) :
    cantorCylinder k ∩ prefixCylinder s =
      if prefixPoint s ∈ cantorCylinder k then prefixCylinder s else ∅ := by
  classical
  ext x
  by_cases hp : prefixPoint s ∈ cantorCylinder k
  · simp only [if_pos hp, mem_inter_iff]
    exact ⟨fun h => h.2,fun hx => ⟨(cantorCylinder_constant_on_prefix k n hk s x hx).mpr hp,hx⟩⟩
  · simp only [if_neg hp, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hxD hxC
    exact hp ((cantorCylinder_constant_on_prefix k n hk s x hxC).mp hxD)

theorem measure_eq_sum_prefix_inter (μ : Measure HaarCantor) (A : Set HaarCantor)
    (hA : MeasurableSet A) (n : ℕ) :
    μ A = ∑ s : Fin n → Bool, μ (A ∩ prefixCylinder s) := by
  have he : (⋃ s : Fin n → Bool, A ∩ prefixCylinder s) = A := by
    rw [← inter_iUnion, prefixCylinder_iUnion, inter_univ]
  have hd : Pairwise (fun (s t : Fin n → Bool) =>
      Disjoint (A ∩ prefixCylinder s) (A ∩ prefixCylinder t)) := by
    intro s t hst
    exact (prefixCylinder_pairwise_disjoint n hst).mono inter_subset_right inter_subset_right
  calc
    μ A = μ (⋃ s : Fin n → Bool, A ∩ prefixCylinder s) := congrArg μ he.symm
    _ = _ := by
      rw [measure_iUnion hd (fun s => hA.inter (isClopen_prefixCylinder s).isClosed.measurableSet),tsum_fintype]

theorem cantorCylinder_mass_prefix_sum (μ : Measure HaarCantor) (k : CantorCylinderIndex) (n : ℕ)
    (hk : ∀ i ∈ k.1, i < n) :
    μ (cantorCylinder k) = ∑ s : Fin n → Bool,
      if prefixPoint s ∈ cantorCylinder k then μ (prefixCylinder s) else 0 := by
  classical
  rw [measure_eq_sum_prefix_inter μ _ (cantorCylinder_measurable k) n]
  apply Finset.sum_congr rfl
  intro s _
  rw [cantorCylinder_inter_prefix k n hk s]
  split_ifs <;> simp



end BenchmarkJump
end
end Source91
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorPrefixFunctions -/
namespace BenchmarkJumpSubmission
section Source92
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def prefixStep {n : ℕ} (a : (Fin n → Bool) → ℝ) : C(HaarCantor,ℝ) :=
  ⟨fun x => a (fun i : Fin n => x i),
    (continuous_of_discreteTopology (f := a)).comp (continuous_pi fun i : Fin n => continuous_apply (i : ℕ))⟩

theorem prefixStep_on_cell {n : ℕ} (a : (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (x : HaarCantor) (hx : x ∈ prefixCylinder s) : prefixStep a x = a s := by
  change a (fun i : Fin n => x i) = a s
  congr 1
  exact funext hx

theorem prefixStep_eq_indicator_sum {n : ℕ} (a : (Fin n → Bool) → ℝ) (x : HaarCantor) :
    prefixStep a x = ∑ s : Fin n → Bool, (prefixCylinder s).indicator (fun _ => a s) x := by
  classical
  let s₀ : Fin n → Bool := fun i => x i
  rw [Finset.sum_eq_single s₀]
  · simp [prefixStep,s₀,prefixCylinder]
  · intro s _hs hne
    have hx : x ∉ prefixCylinder s := by
      intro h
      exact hne (funext h).symm
    simp [Set.indicator_of_notMem hx]
  · simp

theorem integral_prefixStep {n : ℕ} (μ : Measure HaarCantor) [IsFiniteMeasure μ]
    (a : (Fin n → Bool) → ℝ) :
    (∫ x, prefixStep a x ∂μ) = ∑ s : Fin n → Bool, μ.real (prefixCylinder s) * a s := by
  have he : (fun x => prefixStep a x) = fun x => ∑ s : Fin n → Bool,
      (prefixCylinder s).indicator (fun _ => a s) x := funext (prefixStep_eq_indicator_sum a)
  rw [he,integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro s _hs
    simpa only [smul_eq_mul] using integral_indicator_const (μ := μ) (a s)
      (isClopen_prefixCylinder s).isClosed.measurableSet
  · intro s _hs
    exact (integrable_const (a s)).indicator (isClopen_prefixCylinder s).isClosed.measurableSet



end BenchmarkJump
end
end Source92
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureGenericErgodicity -/
namespace BenchmarkJumpSubmission
section Source93
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

abbrev PositiveContinuousWeight := {w : C(HaarCantor, ℝ) | ∀ x, 0 < w x}



/-- Category consequence of the concrete positive continuous reweight
homeomorphisms. The orbit-density premise is a separately tracked remaining
dependency, to be discharged by finite-prefix mass matching. -/
theorem fullSupportMeasureEquivalence_genericallyErgodic_of_dense_reweights
    (hDense : ∀ μ : PositiveCylinderProbabilities,
      Dense (range (fun w : PositiveContinuousWeight => continuousSquareReweight w.1 w.property μ))) :
    GenericallyErgodic FullSupportMeasureEquivalence := by
  classical
  intro A hA hInv
  by_cases hm : IsMeagre A
  · exact Or.inl hm
  right
  obtain ⟨U, hUo, hAU⟩ := hA.residualEq_isOpen
  have hAU' : ∀ᶠ x in residual PositiveCylinderProbabilities, x ∈ A ↔ x ∈ U :=
    Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra hn
    have hUe : U = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hm
    filter_upwards [hAU'] with x hx
    simp [hUe] at hx
    exact hx
  have hMove (x : PositiveCylinderProbabilities) : ∃ w : PositiveContinuousWeight,
      continuousSquareReweight w.1 w.property x ∈ U := by
    obtain ⟨y, hyU, hyRange⟩ := (hDense x).inter_open_nonempty U hUo hUne
    obtain ⟨w, rfl⟩ := hyRange
    exact ⟨w, hyU⟩
  choose w hmem using hMove
  let V : PositiveCylinderProbabilities → Set PositiveCylinderProbabilities :=
    fun x => {y | continuousSquareReweight (w x).1 (w x).property y ∈ U}
  have hVnhds (x : PositiveCylinderProbabilities) : V x ∈ 𝓝 x :=
    (hUo.preimage (continuous_continuousSquareReweight _ _)).mem_nhds (hmem x)
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hVnhds
  have hAll : ∀ᶠ y in residual PositiveCylinderProbabilities, ∀ x ∈ S,
      continuousSquareReweight (w x).1 (w x).property y ∈ A ↔
        continuousSquareReweight (w x).1 (w x).property y ∈ U := by
    apply eventually_countable_ball hScount |>.2
    intro x _hx
    exact tendsto_residual_of_isOpenMap (continuous_continuousSquareReweight _ _)
      (continuousSquareReweightHomeomorph _ _).isOpenMap hAU'
  filter_upwards [hAll] with y hy
  have hyCover : y ∈ ⋃ x ∈ S, V x := by rw [hScover]; trivial
  obtain ⟨x, hx⟩ := mem_iUnion.mp hyCover
  obtain ⟨hxS, hyV⟩ := mem_iUnion.mp hx
  have hyA := (hy x hxS).mpr hyV
  exact (hInv y (continuousSquareReweight (w x).1 (w x).property y)
    (densitySource_target_equivalent (positiveContinuousSection (w x).1 (w x).property y))).mpr hyA



end BenchmarkJump
end
end Source93
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorReweightOrbitDensity -/
namespace BenchmarkJumpSubmission
section Source94
open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

set_option maxHeartbeats 1500000

def matchingPrefixWeight (μ ν : PositiveCylinderProbabilities) (n : ℕ) : C(HaarCantor,ℝ) :=
  prefixStep (fun s : Fin n → Bool => Real.sqrt
    (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) /
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)))

theorem matchingPrefixWeight_positive (μ ν : PositiveCylinderProbabilities) (n : ℕ) :
    ∀ x, 0 < matchingPrefixWeight μ ν n x := by
  intro x
  exact Real.sqrt_pos.mpr (div_pos (ν.property n _) (μ.property n _))

theorem matchingPrefixWeight_square (μ ν : PositiveCylinderProbabilities) (n : ℕ) (x : HaarCantor) :
    (matchingPrefixWeight μ ν n x) ^ 2 =
      prefixStep (fun s : Fin n → Bool =>
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) /
          ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)) x :=
  Real.sq_sqrt (div_nonneg measureReal_nonneg measureReal_nonneg)

theorem matchingPrefixWeight_norm (μ ν : PositiveCylinderProbabilities) (n : ℕ) :
    ‖continuousDensityVector μ (matchingPrefixWeight μ ν n)‖ = 1 := by
  have hn : ‖continuousDensityVector μ (matchingPrefixWeight μ ν n)‖ ^ 2 = 1 := by
    rw [continuousDensityVector_norm_sq]
    simp_rw [matchingPrefixWeight_square]
    rw [integral_prefixStep]
    have hs : ∀ s : Fin n → Bool,
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) *
        (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) /
        ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)) =
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) := by
      intro s
      exact mul_div_cancel₀ _ (μ.property n s).ne'
    simp_rw [hs]
    exact prefixCylinder_mass_sum ν n
  nlinarith [norm_nonneg (continuousDensityVector μ (matchingPrefixWeight μ ν n))]

theorem matchingPrefixWeight_cell_mass (μ ν : PositiveCylinderProbabilities) (n : ℕ)
    (s : Fin n → Bool) :
    ((continuousSquareReweight (matchingPrefixWeight μ ν n) (matchingPrefixWeight_positive μ ν n) μ :
      ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) =
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) := by
  rw [continuousSquareReweight_measure, matchingPrefixWeight_norm]
  simp only [inv_one,one_mul]
  rw [withDensity_apply _ (isClopen_prefixCylinder s).isClosed.measurableSet]
  let a := ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)
  let b := ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)
  have hb : 0 < b := μ.property n s
  have hconst : (fun x => ENNReal.ofReal ((matchingPrefixWeight μ ν n x) ^ 2))
      =ᵐ[(((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).restrict (prefixCylinder s))]
        (fun _ => ENNReal.ofReal (a / b)) := by
    filter_upwards [ae_restrict_mem (isClopen_prefixCylinder s).isClosed.measurableSet] with x hx
    rw [matchingPrefixWeight_square,prefixStep_on_cell _ s x hx]
  rw [lintegral_congr_ae hconst,lintegral_const,Measure.restrict_apply_univ]
  rw [ENNReal.ofReal_div_of_pos hb,ofReal_measureReal,ofReal_measureReal]
  exact ENNReal.div_mul_cancel (by
    intro hzero
    have hz := congrArg ENNReal.toReal hzero
    change b = 0 at hz
    exact hb.ne' hz) (measure_ne_top _ _)

theorem matchingPrefixWeight_cylinder_mass (μ ν : PositiveCylinderProbabilities) (n : ℕ)
    (k : MeasureUnitary.CantorCylinderIndex) (hk : ∀ i ∈ k.1, i < n) :
    ((continuousSquareReweight (matchingPrefixWeight μ ν n) (matchingPrefixWeight_positive μ ν n) μ :
      ProbabilityMeasure HaarCantor) : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) =
      ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) := by
  classical
  rw [cantorCylinder_mass_prefix_sum _ k n hk,cantorCylinder_mass_prefix_sum _ k n hk]
  apply Finset.sum_congr rfl
  intro s _hs
  split_ifs
  · exact matchingPrefixWeight_cell_mass μ ν n s
  · rfl

theorem matchingPrefixWeight_tendsto (μ ν : PositiveCylinderProbabilities) :
    Tendsto (fun n => continuousSquareReweight (matchingPrefixWeight μ ν n)
      (matchingPrefixWeight_positive μ ν n) μ) atTop (𝓝 ν) := by
  apply tendsto_subtype_rng.mpr
  apply (tendsto_cantorProbability_iff _ _).mpr
  intro k
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (k.1.sup id)] with n hn
  exact (congrArg ENNReal.toReal (matchingPrefixWeight_cylinder_mass μ ν n k
    (fun i hi => (Finset.le_sup (f := id) hi).trans_lt hn))).symm

theorem continuousSquareReweight_orbit_dense (μ : PositiveCylinderProbabilities) :
    Dense (range (fun w : PositiveContinuousWeight => continuousSquareReweight w.1 w.property μ)) := by
  intro ν
  apply mem_closure_of_tendsto (matchingPrefixWeight_tendsto μ ν)
  apply Eventually.of_forall
  intro n
  exact ⟨⟨matchingPrefixWeight μ ν n,matchingPrefixWeight_positive μ ν n⟩,rfl⟩

end BenchmarkJump
end
end Source94
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureClassClosedCover -/
namespace BenchmarkJumpSubmission
section Source95
open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def clopenACBound (μ : ProbabilityMeasure HaarCantor) (k : ℕ) :
    Set PositiveCylinderProbabilities :=
  {ν | ∀ A : Set HaarCantor, IsClopen A → (2⁻¹ : ℝ≥0∞) ≤ (μ : Measure HaarCantor) A →
    ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ ≤ ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A}

theorem continuous_clopen_mass_ennreal (A : Set HaarCantor) (hA : IsClopen A) :
    Continuous (fun μ : ProbabilityMeasure HaarCantor => (μ : Measure HaarCantor) A) := by
  have he : (fun μ : ProbabilityMeasure HaarCantor => (μ : Measure HaarCantor) A) =
      (fun μ : ProbabilityMeasure HaarCantor => ENNReal.ofReal ((μ : Measure HaarCantor).real A)) := by
    funext μ
    exact (ENNReal.ofReal_toReal (measure_ne_top (μ : Measure HaarCantor) A)).symm
  rw [he]
  exact ENNReal.continuous_ofReal.comp (continuous_clopen_mass A hA)

theorem isClosed_clopenACBound (μ : ProbabilityMeasure HaarCantor) (k : ℕ) :
    IsClosed (clopenACBound μ k) := by
  simp only [clopenACBound, setOf_forall]
  apply isClosed_iInter
  intro A
  apply isClosed_iInter
  intro hA
  apply isClosed_iInter
  intro _hμA
  exact isClosed_le continuous_const ((continuous_clopen_mass_ennreal A hA).comp continuous_subtype_val)

theorem ac_mem_clopenACBound (μ : ProbabilityMeasure HaarCantor) (ν : PositiveCylinderProbabilities)
    (hac : (μ : Measure HaarCantor) ≪ ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) :
    ∃ k : ℕ, ν ∈ clopenACBound μ k := by
  let ρ : Measure HaarCantor := ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
  letI : IsProbabilityMeasure (μ : Measure HaarCantor) := μ.property
  letI : IsProbabilityMeasure ρ := (ν : ProbabilityMeasure HaarCantor).property
  letI : SFinite (μ : Measure HaarCantor) := inferInstance
  letI : SigmaFinite ρ := inferInstance
  letI : Measure.HaveLebesgueDecomposition (μ : Measure HaarCantor) ρ :=
    Measure.haveLebesgueDecomposition_of_sigmaFinite (μ : Measure HaarCantor) ρ
  change (μ : Measure HaarCantor) ≪ ρ at hac
  have hi : ∫⁻ x, (μ : Measure HaarCantor).rnDeriv ρ x ∂ρ ≠ ∞ := by
    rw [Measure.lintegral_rnDeriv hac]
    exact measure_ne_top _ _
  obtain ⟨δ,hδ,hbound⟩ := exists_pos_setLIntegral_lt_of_measure_lt hi
    (ε := (2⁻¹ : ℝ≥0∞)) (by simp)
  obtain ⟨k,hk⟩ := ENNReal.exists_inv_nat_lt (ne_of_gt hδ)
  refine ⟨k,fun A hA hμA => ?_⟩
  apply le_of_not_gt
  intro hνA
  have hsmall : ρ A < δ := hνA.trans_le
    ((ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.le_succ k)).trans hk.le)
  have hμsmall := hbound A hsmall
  rw [Measure.setLIntegral_rnDeriv' hac hA.isClosed.measurableSet] at hμsmall
  exact (not_lt_of_ge hμA) hμsmall

end BenchmarkJump
end
end Source95
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureClassMeagre -/
namespace BenchmarkJumpSubmission
section Source96
open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

set_option maxHeartbeats 1500000

namespace BenchmarkJump

theorem exists_small_mixing_parameter (ε : ℝ≥0∞) (hε : ε ≠ 0) (hε1 : ε ≤ 1) :
    ∃ t : unitInterval, 0 < (t : ℝ) ∧ ENNReal.ofReal (t : ℝ) < ε := by
  obtain ⟨r,hr,hrε⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := 1) (b := ε) (by simp) hε
  simp only [mul_one] at hrε
  have hr1 : r ≤ 1 := by exact_mod_cast hrε.le.trans hε1
  refine ⟨⟨(r : ℝ), r.coe_nonneg, by exact_mod_cast hr1⟩, by exact_mod_cast hr, ?_⟩
  simpa using hrε

theorem redirectedProbability_compl_small (μ ν : ProbabilityMeasure HaarCantor) (n m : ℕ) :
    (redirectedProbability μ ν n m : Measure HaarCantor) (smallPrefixRegion μ n m)ᶜ = 0 := by
  rw [show (redirectedProbability μ ν n m : Measure HaarCantor) =
      (ν : Measure HaarCantor).map (prefixRedirect μ n m) from rfl,
    Measure.map_apply (continuous_prefixRedirect μ n m).measurable
      (smallPrefixRegion_clopen μ n m).isClosed.measurableSet.compl]
  have he : prefixRedirect μ n m ⁻¹' (smallPrefixRegion μ n m)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx (prefixRedirect_mem_smallPrefixRegion μ n m x)
  rw [he,measure_empty]

theorem smallPrefixRegion_compl_large (μ : ProbabilityMeasure HaarCantor) (n : ℕ) :
    (2⁻¹ : ℝ≥0∞) ≤ (μ : Measure HaarCantor) (smallPrefixRegion μ n 2)ᶜ := by
  have hsmall := smallPrefixRegion_mass_bound μ n 2
  have hsum := measureReal_add_measureReal_compl (μ := (μ : Measure HaarCantor))
    (smallPrefixRegion_clopen μ n 2).isClosed.measurableSet
  have hr : (1 / 2 : ℝ) ≤ (μ : Measure HaarCantor).real (smallPrefixRegion μ n 2)ᶜ := by
    norm_num at hsmall hsum ⊢
    linarith
  apply (ENNReal.toReal_le_toReal (by simp) (measure_ne_top _ _)).mp
  simpa using hr

theorem fullSupport_redirected_tendsto (μ : ProbabilityMeasure HaarCantor)
    (ν : PositiveCylinderProbabilities) (t : unitInterval) (ht : 0 < (t : ℝ)) :
    Tendsto (fun n => fullSupportMix t ht (redirectedProbability μ ν n 2) ν) atTop (𝓝 ν) := by
  have h : Tendsto (fun p : ProbabilityMeasure HaarCantor × PositiveCylinderProbabilities =>
      fullSupportMix t ht p.1 p.2) (𝓝 ((ν : ProbabilityMeasure HaarCantor),ν))
      (𝓝 (fullSupportMix t ht (ν : ProbabilityMeasure HaarCantor) ν)) :=
    (continuous_fullSupportMix t ht).tendsto ((ν : ProbabilityMeasure HaarCantor),ν)
  have hp : Tendsto (fun n => (redirectedProbability μ ν n 2,ν)) atTop
      (𝓝 ((ν : ProbabilityMeasure HaarCantor),ν)) :=
    (redirectedProbability_tendsto μ ν 2).prodMk_nhds (tendsto_const_nhds (x := ν))
  have he : fullSupportMix t ht (ν : ProbabilityMeasure HaarCantor) ν = ν :=
    Subtype.ext (cantorProbabilityMix_self t ν)
  simpa only [he] using h.comp hp

theorem fullSupport_redirected_outside (μ : ProbabilityMeasure HaarCantor)
    (ν : PositiveCylinderProbabilities) (k : ℕ) (t : unitInterval) (ht : 0 < (t : ℝ))
    (htsmall : ENNReal.ofReal (t : ℝ) < ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) (n : ℕ) :
    fullSupportMix t ht (redirectedProbability μ ν n 2) ν ∉ clopenACBound μ k := by
  intro h
  let A := (smallPrefixRegion μ n 2)ᶜ
  have hA : IsClopen A := (smallPrefixRegion_clopen μ n 2).compl
  have hlower := h A hA (smallPrefixRegion_compl_large μ n)
  have hupper : ((fullSupportMix t ht (redirectedProbability μ ν n 2) ν :
      ProbabilityMeasure HaarCantor) : Measure HaarCantor) A ≤ ENNReal.ofReal (t : ℝ) := by
    change (cantorProbabilityMix t (redirectedProbability μ ν n 2) ν : Measure HaarCantor) A ≤ _
    rw [cantorProbabilityMix_apply, redirectedProbability_compl_small, mul_zero, zero_add]
    have hνA : ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A ≤ 1 := by
      simpa using (measure_mono (subset_univ A) :
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) A ≤
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) univ)
    simpa only [mul_one] using mul_le_mul_left' hνA (ENNReal.ofReal (t : ℝ))
  exact (not_lt_of_ge hlower) (hupper.trans_lt htsmall)

theorem isNowhereDense_clopenACBound (μ : ProbabilityMeasure HaarCantor) (k : ℕ) :
    IsNowhereDense (clopenACBound μ k) := by
  apply (isClosed_clopenACBound μ k).isNowhereDense_iff.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro ν hν
  obtain ⟨t,ht,htsmall⟩ := exists_small_mixing_parameter (((k + 1 : ℕ) : ℝ≥0∞)⁻¹)
    (by simp) (ENNReal.inv_le_one.mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)))
  have hlim := fullSupport_redirected_tendsto μ ν t ht
  have hev := hlim.eventually (isOpen_interior.mem_nhds hν)
  obtain ⟨n,hn⟩ := hev.exists
  exact fullSupport_redirected_outside μ ν k t ht htsmall n (interior_subset hn)

theorem measure_ac_class_meagre (μ : ProbabilityMeasure HaarCantor) :
    IsMeagre {ν : PositiveCylinderProbabilities |
      (μ : Measure HaarCantor) ≪ ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor)} := by
  apply (isMeagre_iUnion (fun k => (isNowhereDense_clopenACBound μ k).isMeagre)).mono
  intro ν hν
  obtain ⟨k,hk⟩ := ac_mem_clopenACBound μ ν hν
  exact mem_iUnion.mpr ⟨k,hk⟩

theorem measure_equivalence_class_meagre (μ : PositiveCylinderProbabilities) :
    IsMeagre {ν : PositiveCylinderProbabilities |
      (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
          ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ∧
        ((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor) ≪
          ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor))} :=
  (measure_ac_class_meagre μ).mono (fun _ h => h.1)

end BenchmarkJump
end
end Source96
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorFullSupportWitness -/
namespace BenchmarkJumpSubmission
section Source97
open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace BenchmarkJump

def fairCantorLaw : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance fairCantorLaw_probability : IsProbabilityMeasure fairCantorLaw := by
  constructor
  norm_num [fairCantorLaw,ENNReal.inv_two_add_inv_two]

theorem fairCantorLaw_singleton (b : Bool) : fairCantorLaw {b} = (1 / 2 : ℝ≥0∞) := by
  cases b <;> norm_num [fairCantorLaw,Measure.dirac_apply]

def fairCantorProbability : ProbabilityMeasure HaarCantor :=
  ⟨Measure.infinitePi (fun _ : ℕ => fairCantorLaw),inferInstance⟩

theorem fairCantorProbability_prefix {n : ℕ} (s : Fin n → Bool) :
    (fairCantorProbability : Measure HaarCantor) (prefixCylinder s) = (1 / 2 : ℝ≥0∞) ^ n := by
  classical
  let sets : ℕ → Set Bool := fun i => if hi : i < n then {s ⟨i,hi⟩} else univ
  have he : prefixCylinder s = (Finset.range n : Set ℕ).pi sets := by
    ext x
    constructor
    · intro hx i hi
      have hin := Finset.mem_range.mp hi
      simpa [sets,hin] using hx ⟨i,hin⟩
    · intro hx i
      have h := hx i (Finset.mem_range.mpr i.isLt)
      simpa [sets,i.isLt] using h
  rw [he]
  change Measure.infinitePi (fun _ : ℕ => fairCantorLaw) ((Finset.range n : Set ℕ).pi sets) = _
  rw [Measure.infinitePi_pi _ (fun i hi => by simp [sets,Finset.mem_range.mp hi])]
  have ht : ∀ i ∈ Finset.range n, fairCantorLaw (sets i) = (1 / 2 : ℝ≥0∞) := by
    intro i hi
    simp [sets,Finset.mem_range.mp hi,fairCantorLaw_singleton]
  simp_rw [Finset.prod_congr rfl ht]
  simp

theorem fairCantorProbability_fullSupport : fairCantorProbability ∈ PositiveCylinderProbabilities := by
  intro n s
  rw [measureReal_def,fairCantorProbability_prefix,ENNReal.toReal_pow]
  norm_num

def fairFullSupportProbability : PositiveCylinderProbabilities :=
  ⟨fairCantorProbability,fairCantorProbability_fullSupport⟩

instance positiveCylinderProbabilities_nonempty : Nonempty PositiveCylinderProbabilities :=
  ⟨fairFullSupportProbability⟩

end BenchmarkJump
end
end Source97
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureCategory -/
namespace BenchmarkJumpSubmission
section Source98
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

theorem fullSupportMeasureEquivalence_genericallyErgodic :
    GenericallyErgodic FullSupportMeasureEquivalence :=
  fullSupportMeasureEquivalence_genericallyErgodic_of_dense_reweights
    continuousSquareReweight_orbit_dense

theorem fullSupportMeasureEquivalence_class_meagre (μ : PositiveCylinderProbabilities) :
    IsMeagre {ν | FullSupportMeasureEquivalence ν μ} := by
  apply (measure_equivalence_class_meagre μ).mono
  intro ν hν
  exact ⟨hν.2, hν.1⟩




end BenchmarkJump
end
end Source98
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityMixOpenWeights -/
namespace BenchmarkJumpSubmission
section Source99
/-! Positive finite-partition reweighting of a full-support Cantor probability. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def prefixReweightMeasure (ρ : ProbabilityMeasure HaarCantor) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) : Measure HaarCantor :=
  ∑ s : Fin n → Bool, (w s / (ρ : Measure HaarCantor) (prefixCylinder s)) •
    (ρ : Measure HaarCantor).restrict (prefixCylinder s)

lemma positive_prefix_mass_ne_zero (ρ : PositiveCylinderProbabilities)
    (n : ℕ) (s : Fin n → Bool) :
    (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder s) ≠ 0 :=
  (ENNReal.toReal_pos_iff.mp (ρ.property n s)).1.ne'

lemma prefix_restriction_sum (ρ : ProbabilityMeasure HaarCantor) (n : ℕ) :
    (∑ s : Fin n → Bool, (ρ : Measure HaarCantor).restrict (prefixCylinder s)) =
      (ρ : Measure HaarCantor) := by
  have h := Measure.restrict_iUnion (μ := (ρ : Measure HaarCantor))
    (prefixCylinder_pairwise_disjoint n)
    (fun s => (isClopen_prefixCylinder s).isClosed.measurableSet)
  rw [prefixCylinder_iUnion, Measure.restrict_univ, Measure.sum_fintype] at h
  exact h.symm

lemma prefixReweightMeasure_univ (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) :
    prefixReweightMeasure ρ n w univ = ∑ s, w s := by
  simp only [prefixReweightMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply_univ]
  apply Finset.sum_congr rfl
  intro s _
  exact ENNReal.div_mul_cancel (positive_prefix_mass_ne_zero ρ n s)
    (measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _)

lemma prefixReweightMeasure_cell (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (t : Fin n → Bool) :
    prefixReweightMeasure ρ n w (prefixCylinder t) = w t := by
  classical
  simp only [prefixReweightMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.restrict_apply (isClopen_prefixCylinder t).isClosed.measurableSet]
  rw [Finset.sum_eq_single t]
  · rw [inter_self]
    exact ENNReal.div_mul_cancel (positive_prefix_mass_ne_zero ρ n t)
      (measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _)
  · intro s _ hst
    rw [(prefixCylinder_pairwise_disjoint n (Ne.symm hst)).inter_eq, measure_empty, mul_zero]
  · simp

lemma prefixReweightMeasure_dominates (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (hw : ∀ s, w s ≠ 0) :
    (ρ : ProbabilityMeasure HaarCantor).toMeasure ≪ prefixReweightMeasure ρ n w := by
  rw [← prefix_restriction_sum ρ n]
  rw [prefixReweightMeasure, ← Measure.sum_fintype, ← Measure.sum_fintype]
  apply Measure.absolutelyContinuous_sum_left
  intro s
  apply Measure.absolutelyContinuous_sum_right s
  apply Measure.absolutelyContinuous_smul
  exact ENNReal.div_ne_zero.mpr ⟨hw s, measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _⟩

def prefixReweightProbability (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (hw : ∑ s, w s = 1) : ProbabilityMeasure HaarCantor :=
  ⟨prefixReweightMeasure ρ n w, ⟨(prefixReweightMeasure_univ ρ n w).trans hw⟩⟩

def positivePrefixReweight (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ≥0∞) (hw : ∑ s, w s = 1) (hpos : ∀ s, w s ≠ 0) :
    PositiveCylinderProbabilities :=
  ⟨prefixReweightProbability ρ n w hw, by
    intro m t
    have hρpos : 0 < (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder t) :=
      (ENNReal.toReal_pos_iff.mp (ρ.property m t)).1
    have hpos' := (prefixReweightMeasure_dominates ρ n w hpos).pos_mono hρpos
    exact ENNReal.toReal_pos hpos'.ne' (measure_ne_top (prefixReweightProbability ρ n w hw).toMeasure _)⟩

theorem prefixReweightMeasure_mix (t : unitInterval) (ρ : PositiveCylinderProbabilities)
    (n : ℕ) (u v : (Fin n → Bool) → ℝ≥0∞)
    (hmix : ∀ s, ENNReal.ofReal (1 - (t : ℝ)) * u s + ENNReal.ofReal (t : ℝ) * v s =
      (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder s)) :
    ENNReal.ofReal (1 - (t : ℝ)) • prefixReweightMeasure ρ n u +
      ENNReal.ofReal (t : ℝ) • prefixReweightMeasure ρ n v =
        (ρ : ProbabilityMeasure HaarCantor).toMeasure := by
  classical
  calc
    _ = ∑ s : Fin n → Bool,
        ((ENNReal.ofReal (1 - (t : ℝ)) * u s + ENNReal.ofReal (t : ℝ) * v s) /
          (ρ : ProbabilityMeasure HaarCantor).toMeasure (prefixCylinder s)) •
          (ρ : ProbabilityMeasure HaarCantor).toMeasure.restrict (prefixCylinder s) := by
      simp only [prefixReweightMeasure, Finset.smul_sum, ← Finset.sum_add_distrib, smul_smul]
      apply Finset.sum_congr rfl
      intro s _
      rw [← add_smul]
      congr 1
      simp only [div_eq_mul_inv]
      ring
    _ = ∑ s : Fin n → Bool,
        (ρ : ProbabilityMeasure HaarCantor).toMeasure.restrict (prefixCylinder s) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [hmix, ENNReal.div_self (positive_prefix_mass_ne_zero ρ n s)
        (measure_ne_top (ρ : ProbabilityMeasure HaarCantor).toMeasure _), one_smul]
    _ = _ := prefix_restriction_sum ρ n

end BenchmarkJump
end
end Source99
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityMixOpenContinuity -/
namespace BenchmarkJumpSubmission
section Source100
/-! Weak continuity of the positive finite-cell reweighting operation. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def realPrefixReweight (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ) (hw : ∑ s, w s = 1) (hpos : ∀ s, 0 < w s) :
    PositiveCylinderProbabilities :=
  positivePrefixReweight ρ n (fun s => ENNReal.ofReal (w s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => (hpos s).le), hw, ENNReal.ofReal_one])
    (fun s => (ENNReal.ofReal_pos.mpr (hpos s)).ne')

lemma realPrefixReweight_real (ρ : PositiveCylinderProbabilities) (n : ℕ)
    (w : (Fin n → Bool) → ℝ) (hw : ∑ s, w s = 1) (hpos : ∀ s, 0 < w s)
    (A : Set HaarCantor) (hA : MeasurableSet A) :
    ((realPrefixReweight ρ n w hw hpos : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real A =
      ∑ s : Fin n → Bool, (w s /
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)) *
        ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (A ∩ prefixCylinder s) := by
  change (prefixReweightMeasure ρ n (fun s => ENNReal.ofReal (w s)) A).toReal = _
  rw [prefixReweightMeasure, Measure.finsetSum_apply, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro s _
    simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (hpos s).le, Measure.restrict_apply hA, measureReal_def]
  · intro s _
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top
      (ENNReal.div_ne_top ENNReal.ofReal_ne_top (positive_prefix_mass_ne_zero ρ n s))
      (measure_ne_top (((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).restrict (prefixCylinder s)) A)

theorem continuous_realPrefixReweight {T : Type*} [TopologicalSpace T]
    (ρ : T → PositiveCylinderProbabilities) (hρ : Continuous ρ)
    (n : ℕ) (w : T → (Fin n → Bool) → ℝ) (hwc : ∀ s, Continuous (fun x => w x s))
    (hw : ∀ x, ∑ s, w x s = 1) (hpos : ∀ x s, 0 < w x s) :
    Continuous (fun x => realPrefixReweight (ρ x) n (w x) (hw x) (hpos x)) := by
  apply Continuous.subtype_mk
  apply (continuous_cantorProbability_iff _).mpr
  intro k
  change Continuous (fun x =>
    ((realPrefixReweight (ρ x) n (w x) (hw x) (hpos x) : ProbabilityMeasure HaarCantor) :
      Measure HaarCantor).real (MeasureUnitary.cantorCylinder k))
  simp_rw [realPrefixReweight_real _ _ _ _ _ _ (MeasureUnitary.cantorCylinder_measurable k)]
  apply continuous_finsetSum
  intro s _
  have hc := (continuous_clopen_mass (prefixCylinder s) (isClopen_prefixCylinder s)).comp
    (continuous_subtype_val.comp hρ)
  have hi := (continuous_clopen_mass (MeasureUnitary.cantorCylinder k ∩ prefixCylinder s)
    ((isClopen_cantorCylinder k).inter (isClopen_prefixCylinder s))).comp
      (continuous_subtype_val.comp hρ)
  exact ((hwc s).div hc (fun x => (ρ x).property n s |>.ne')).mul hi

def prefixResample (ρ μ : PositiveCylinderProbabilities) (n : ℕ) : PositiveCylinderProbabilities :=
  realPrefixReweight ρ n
    (fun s => ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s))
    (prefixCylinder_mass_sum μ n) (μ.property n)

lemma prefixResample_cell (ρ μ : PositiveCylinderProbabilities) (n : ℕ) (s : Fin n → Bool) :
    ((prefixResample ρ μ n : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) =
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (prefixCylinder s) := by
  change prefixReweightMeasure ρ n _ _ = _
  rw [prefixReweightMeasure_cell]
  change ENNReal.ofReal (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
    (prefixCylinder s)).toReal = _
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

lemma prefixResample_cylinder (ρ μ : PositiveCylinderProbabilities) (n : ℕ)
    (k : MeasureUnitary.CantorCylinderIndex) (hk : ∀ i ∈ k.1, i < n) :
    ((prefixResample ρ μ n : ProbabilityMeasure HaarCantor) : Measure HaarCantor)
      (MeasureUnitary.cantorCylinder k) =
    ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor) (MeasureUnitary.cantorCylinder k) := by
  classical
  rw [cantorCylinder_mass_prefix_sum _ k n hk, cantorCylinder_mass_prefix_sum _ k n hk]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs
  · exact prefixResample_cell ρ μ n s
  · rfl

theorem tendsto_prefixResample (ρ μ : PositiveCylinderProbabilities) :
    Tendsto (fun n : ℕ => prefixResample ρ μ n) atTop (𝓝 μ) := by
  apply tendsto_subtype_rng.mpr
  apply (tendsto_cantorProbability_iff _ _).mpr
  intro k
  apply Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (k.1.sup id)] with n hn
  exact congrArg ENNReal.toReal (prefixResample_cylinder ρ μ n k
    (fun i hi => (Finset.le_sup (f := id) hi).trans_lt hn)).symm

end BenchmarkJump
end
end Source100
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityMixOpenSection -/
namespace BenchmarkJumpSubmission
section Source101
/-! Continuous local right inverses of the probability mixture map, through
the finite-prefix resamplings of its two original endpoints. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

def mixLiftWeights (μ β ρ : PositiveCylinderProbabilities) (n : ℕ) (s : Fin n → Bool) : ℝ :=
  ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) +
    ((ρ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s) -
    ((β : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)

lemma mixLiftWeights_sum (μ β ρ : PositiveCylinderProbabilities) (n : ℕ) :
    ∑ s, mixLiftWeights μ β ρ n s = 1 := by
  simp only [mixLiftWeights, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [prefixCylinder_mass_sum μ n, prefixCylinder_mass_sum ρ n, prefixCylinder_mass_sum β n]
  norm_num

lemma continuous_mixLiftWeights (μ β : PositiveCylinderProbabilities) (n : ℕ) (s : Fin n → Bool) :
    Continuous (fun ρ => mixLiftWeights μ β ρ n s) := by
  exact (continuous_const.add ((continuous_clopen_mass _ (isClopen_prefixCylinder s)).comp
    continuous_subtype_val)).sub continuous_const

def mixLiftDomain (μ ν β : PositiveCylinderProbabilities) (n : ℕ) : Set PositiveCylinderProbabilities :=
  {ρ | ∀ s : Fin n → Bool, 0 < mixLiftWeights μ β ρ n s ∧ 0 < mixLiftWeights ν β ρ n s}

lemma isOpen_mixLiftDomain (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    IsOpen (mixLiftDomain μ ν β n) := by
  unfold mixLiftDomain
  simp only [setOf_forall, setOf_and]
  apply isOpen_iInter_of_finite
  intro s
  exact (isOpen_lt continuous_const (continuous_mixLiftWeights μ β n s)).inter
    (isOpen_lt continuous_const (continuous_mixLiftWeights ν β n s))

lemma mixLiftDomain_base (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    β ∈ mixLiftDomain μ ν β n := by
  intro s
  simpa only [mixLiftWeights, add_sub_cancel_right] using ⟨μ.property n s, ν.property n s⟩

def mixLiftLeft (μ ν β : PositiveCylinderProbabilities) (n : ℕ)
    (ρ : mixLiftDomain μ ν β n) : PositiveCylinderProbabilities :=
  realPrefixReweight ρ n (mixLiftWeights μ β ρ n)
    (mixLiftWeights_sum μ β ρ n) (fun s => (ρ.property s).1)

def mixLiftRight (μ ν β : PositiveCylinderProbabilities) (n : ℕ)
    (ρ : mixLiftDomain μ ν β n) : PositiveCylinderProbabilities :=
  realPrefixReweight ρ n (mixLiftWeights ν β ρ n)
    (mixLiftWeights_sum ν β ρ n) (fun s => (ρ.property s).2)

lemma continuous_mixLiftLeft (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    Continuous (mixLiftLeft μ ν β n) :=
  continuous_realPrefixReweight _ continuous_subtype_val n _
    (fun s => (continuous_mixLiftWeights μ β n s).comp continuous_subtype_val)
    _ _

lemma continuous_mixLiftRight (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    Continuous (mixLiftRight μ ν β n) :=
  continuous_realPrefixReweight _ continuous_subtype_val n _
    (fun s => (continuous_mixLiftWeights ν β n s).comp continuous_subtype_val)
    _ _

lemma mixLiftLeft_base (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    mixLiftLeft μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩ = prefixResample β μ n := by
  apply Subtype.ext
  apply Subtype.ext
  change prefixReweightMeasure β n (fun s => ENNReal.ofReal (mixLiftWeights μ β β n s)) =
    prefixReweightMeasure β n (fun s => ENNReal.ofReal
      (((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)))
  congr 1
  funext s
  simp only [mixLiftWeights, add_sub_cancel_right]

lemma mixLiftRight_base (μ ν β : PositiveCylinderProbabilities) (n : ℕ) :
    mixLiftRight μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩ = prefixResample β ν n := by
  apply Subtype.ext
  apply Subtype.ext
  change prefixReweightMeasure β n (fun s => ENNReal.ofReal (mixLiftWeights ν β β n s)) =
    prefixReweightMeasure β n (fun s => ENNReal.ofReal
      (((ν : ProbabilityMeasure HaarCantor) : Measure HaarCantor).real (prefixCylinder s)))
  congr 1
  funext s
  simp only [mixLiftWeights, add_sub_cancel_right]

theorem mixLift_exact (t : unitInterval) (μ ν : PositiveCylinderProbabilities) (n : ℕ)
    (ρ : mixLiftDomain μ ν (positiveProbabilityMix t μ ν) n) :
    positiveProbabilityMix t (mixLiftLeft μ ν (positiveProbabilityMix t μ ν) n ρ)
      (mixLiftRight μ ν (positiveProbabilityMix t μ ν) n ρ) = (ρ : PositiveCylinderProbabilities) := by
  apply Subtype.ext
  apply Subtype.ext
  apply prefixReweightMeasure_mix
  intro s
  have hreal : (1 - (t : ℝ)) * mixLiftWeights μ (positiveProbabilityMix t μ ν) ρ n s +
      (t : ℝ) * mixLiftWeights ν (positiveProbabilityMix t μ ν) ρ n s =
        ((ρ : PositiveCylinderProbabilities) : ProbabilityMeasure HaarCantor).toMeasure.real (prefixCylinder s) := by
    unfold mixLiftWeights
    change (1 - (t : ℝ)) * (_ + _ - (cantorProbabilityMix t μ ν : Measure HaarCantor).real _) +
      (t : ℝ) * (_ + _ - (cantorProbabilityMix t μ ν : Measure HaarCantor).real _) = _
    rw [cantorProbabilityMix_real]
    ring
  change ENNReal.ofReal (1 - (t : ℝ)) * ENNReal.ofReal (mixLiftWeights μ (positiveProbabilityMix t μ ν) ρ n s) +
      ENNReal.ofReal (t : ℝ) * ENNReal.ofReal (mixLiftWeights ν (positiveProbabilityMix t μ ν) ρ n s) = _
  rw [← ENNReal.ofReal_mul (sub_nonneg.mpr t.property.2),
    ← ENNReal.ofReal_mul t.property.1,
    ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.mpr t.property.2) ((ρ.property s).1.le))
      (mul_nonneg t.property.1 ((ρ.property s).2.le)), hreal]
  exact ENNReal.ofReal_toReal (measure_ne_top _ _)

end BenchmarkJump
end
end Source101
end BenchmarkJumpSubmission

/- Preserved source skeleton: CantorProbabilityMixOpen -/
namespace BenchmarkJumpSubmission
section Source102
/-! The affine mixture map is open on the full-support Cantor probabilities,
including the two endpoint parameters. -/

open MeasureTheory Set Filter Topology
open scoped ENNReal Topology

noncomputable section

namespace BenchmarkJump

theorem isOpenMap_positiveProbabilityMix (t : unitInterval) :
    IsOpenMap (fun p : PositiveCylinderProbabilities × PositiveCylinderProbabilities =>
      positiveProbabilityMix t p.1 p.2) := by
  intro O hO
  apply isOpen_iff_mem_nhds.mpr
  rintro β ⟨⟨μ, ν⟩, hμν, rfl⟩
  let β := positiveProbabilityMix t μ ν
  have hlim : Tendsto (fun n : ℕ => (prefixResample β μ n, prefixResample β ν n))
      atTop (𝓝 (μ, ν)) :=
    (tendsto_prefixResample β μ).prodMk_nhds (tendsto_prefixResample β ν)
  have hOev : ∀ᶠ n : ℕ in atTop, (prefixResample β μ n, prefixResample β ν n) ∈ O :=
    hlim (hO.mem_nhds hμν)
  obtain ⟨n, hn⟩ := hOev.exists
  let R := mixLiftDomain μ ν β n
  let b : R := ⟨β, mixLiftDomain_base μ ν β n⟩
  let L : R → PositiveCylinderProbabilities := mixLiftLeft μ ν β n
  let H : R → PositiveCylinderProbabilities := mixLiftRight μ ν β n
  have hc : Continuous (fun r : R => (L r, H r)) :=
    (continuous_mixLiftLeft μ ν β n).prodMk (continuous_mixLiftRight μ ν β n)
  have hb : (L b, H b) ∈ O := by
    change (mixLiftLeft μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩,
      mixLiftRight μ ν β n ⟨β, mixLiftDomain_base μ ν β n⟩) ∈ O
    rwa [mixLiftLeft_base, mixLiftRight_base]
  let N : Set PositiveCylinderProbabilities :=
    (Subtype.val : R → PositiveCylinderProbabilities) '' ((fun r : R => (L r, H r)) ⁻¹' O)
  have hNo : IsOpen N := (isOpen_mixLiftDomain μ ν β n).isOpenMap_subtype_val _ (hO.preimage hc)
  have hbN : β ∈ N := ⟨b, hb, rfl⟩
  apply Filter.mem_of_superset (hNo.mem_nhds hbN)
  intro ρ hρ
  obtain ⟨r, hr, rfl⟩ := hρ
  refine ⟨(L r, H r), hr, ?_⟩
  exact mixLift_exact t μ ν n r

end BenchmarkJump
end
end Source102
end BenchmarkJumpSubmission

/- Preserved source skeleton: WeakGiryInclusion -/
namespace BenchmarkJumpSubmission
section Source103
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩

/-- The weak-Borel full-support source includes measurably into the exact
canonical Giry measurable space of Cantor probability measures. -/
theorem measurable_fullSupport_probability_inclusion :
    Measurable (fun μ : PositiveCylinderProbabilities => (μ : ProbabilityMeasure HaarCantor)) := by
  have hMeasure : Measurable (fun μ : PositiveCylinderProbabilities =>
      ((μ : ProbabilityMeasure HaarCantor) : Measure HaarCantor)) := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      MeasureUnitary.cantorCylinder_generates.symm MeasureUnitary.cantorCylinder_isPiSystem
    rintro A ⟨k, rfl⟩
    exact ((continuous_clopen_mass_ennreal _ (isClopen_cantorCylinder k)).comp
      continuous_subtype_val).measurable
  exact hMeasure.subtype_mk (h := fun μ => (μ : ProbabilityMeasure HaarCantor).property)



end BenchmarkJump
end
end Source103
end BenchmarkJumpSubmission

/- Preserved source skeleton: MeasureJumpObstruction -/
namespace BenchmarkJumpSubmission
section Source104
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

local instance : PolishSpace PositiveCylinderProbabilities := positiveCylinderProbabilities_polish
local instance : MeasurableSpace PositiveCylinderProbabilities := borel PositiveCylinderProbabilities
local instance : BorelSpace PositiveCylinderProbabilities := ⟨rfl⟩

/-- The unconditional local output-row property for actual measure equivalence.
All bundle, Hellinger, interpolation, and category inputs have been proved. -/
theorem measure_local_rows
    (F : PositiveCylinderProbabilities → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism FullSupportMeasureEquivalence (Jump BoundedDifference) F) :
    LocallyGenericallyConstantRows BoundedDifference F := by
  intro k A hAo hAn
  obtain ⟨O, D, ε, n, hOo, hOn, hOA, hOconvex, hε, hD, _hf, hSmall⟩ :=
    measure_local_small_rows F hFm hF k A hAo hAn
  obtain ⟨a, ha⟩ := measure_interpolation_constant_on_open isOpenMap_positiveProbabilityMix
    O hOo hOn hOconvex D hD (fun μ => F μ k) ε hε
    (fun μ hμ ν hν hμD hνD hE => ⟨n, hSmall μ hμ ν hν hμD hνD hE⟩)
  exact ⟨O, a, hOo, hOn, hOA, ha⟩

/-- Actual full-support Cantor measure equivalence has no Borel reduction
to the Friedman--Stanley jump of bounded difference. -/
theorem fullSupport_measure_not_borel_reducible_to_jump :
    ¬ ∃ F : PositiveCylinderProbabilities → ℕ → RealSequences, Measurable F ∧
      ∀ μ ν, FullSupportMeasureEquivalence μ ν ↔ Jump BoundedDifference (F μ) (F ν) :=
  not_borel_reduction_of_local_rows FullSupportMeasureEquivalence BoundedDifference
    boundedDifference_equivalence measurableSet_boundedDifference
    fullSupportMeasureEquivalence_genericallyErgodic fullSupportMeasureEquivalence_class_meagre
    measure_local_rows

/-- The measure-equivalence half of Theorem1.4 on the complete actual space
of Cantor probability measures. -/
theorem measure_not_borel_reducible_to_boundedDifferenceJump :
    ¬ ∃ F : ProbabilityMeasure HaarCantor → ℕ → RealSequences, Measurable F ∧
      ∀ μ ν : ProbabilityMeasure HaarCantor,
        (((μ : Measure HaarCantor) ≪ (ν : Measure HaarCantor)) ∧
          ((ν : Measure HaarCantor) ≪ (μ : Measure HaarCantor))) ↔
        Jump BoundedDifference (F μ) (F ν) := by
  rintro ⟨F, hFm, hRed⟩
  apply fullSupport_measure_not_borel_reducible_to_jump
  refine ⟨F ∘ Subtype.val, hFm.comp measurable_fullSupport_probability_inclusion, ?_⟩
  intro μ ν
  exact hRed μ ν





end BenchmarkJump
end
end Source104
end BenchmarkJumpSubmission

theorem solution : _root_.BenchmarkComparisons.JumpObstructions := by
  constructor
  · exact _root_.BenchmarkComparisons.c0_jump_obstruction
  · rintro ⟨F, hFm, hRed⟩
    apply BenchmarkJumpSubmission.BenchmarkJump.measure_not_borel_reducible_to_boundedDifferenceJump
    refine ⟨F, hFm, ?_⟩
    intro μ ν
    apply (hRed μ ν).trans
    simp only [_root_.BenchmarkComparisons.Jump, BenchmarkJumpSubmission.BenchmarkJump.Jump,
      _root_.BenchmarkComparisons.BoundedDifference,
      ← BenchmarkJumpSubmission.BenchmarkJump.boundedDifference_iff_real_bound]

#print axioms solution
