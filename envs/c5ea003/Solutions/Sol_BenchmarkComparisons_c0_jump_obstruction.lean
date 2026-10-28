-- Prove2me | solution 1 for BenchmarkComparisons.c0_jump_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T07:51:02.183725+00:00
-- url     : https://prove2.me/submissions/923842bb-252b-4536-93ee-ae8620ffe495

import Definitions.Def_BenchmarkRelations
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.Tactic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Bases
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.OpenPartialHomeomorph.Basic


/- Whole source module: JumpRows -/
namespace BenchmarkJumpProof
section Source0
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
end Source0
end BenchmarkJumpProof

/- Whole source module: BoundedDifferenceJump -/
namespace BenchmarkJumpProof
section Source1
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

def BoundedDifferenceJump : (ℕ → RealSequences) → (ℕ → RealSequences) → Prop :=
  Jump BoundedDifference

theorem boundedDifferenceJump_equivalence : Equivalence BoundedDifferenceJump :=
  jump_equivalence BoundedDifference boundedDifference_equivalence

theorem measurableSet_boundedDifferenceJump :
    MeasurableSet {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
      BoundedDifferenceJump p.1 p.2} := by
  have hOne (k l : ℕ) : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        BoundedDifference (p.1 k) (p.2 l)} := by
    have hm : Measurable (fun p : (ℕ → RealSequences) × (ℕ → RealSequences) =>
        (p.1 k, p.2 l)) :=
      ((measurable_pi_apply k).comp measurable_fst).prodMk
        ((measurable_pi_apply l).comp measurable_snd)
    exact measurableSet_boundedDifference.preimage hm
  have hFwd : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        ∀ k, ∃ l, BoundedDifference (p.1 k) (p.2 l)} := by
    simpa only [setOf_forall, setOf_exists] using
      MeasurableSet.iInter (fun k => MeasurableSet.iUnion (hOne k))
  have hRev : MeasurableSet
      {p : (ℕ → RealSequences) × (ℕ → RealSequences) |
        ∀ l, ∃ k, BoundedDifference (p.1 k) (p.2 l)} := by
    simpa only [setOf_forall, setOf_exists] using
      MeasurableSet.iInter (fun l => MeasurableSet.iUnion (fun k => hOne k l))
  exact hFwd.inter hRev





end BenchmarkJump
end Source1
end BenchmarkJumpProof

/- Whole source module: CategoryTools -/
namespace BenchmarkJumpProof
section Source2
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
end Source2
end BenchmarkJumpProof

/- Whole source module: CategoryLocal -/
namespace BenchmarkJumpProof
section Source3
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
end Source3
end BenchmarkJumpProof

/- Whole source module: CircleReduction -/
namespace BenchmarkJumpProof
section Source4
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
end Source4
end BenchmarkJumpProof

/- Whole source module: CircleCategory -/
namespace BenchmarkJumpProof
section Source5
/-! The concrete category properties of null difference on the compact
product of circles. These are the source-side category hypotheses of the
first jump obstruction, proved here without assuming the obstruction. -/

open Filter Set Topology TopologicalSpace
open scoped Topology

namespace BenchmarkJump

abbrev CircleSequences := ℕ → UnitAddCircle
abbrev CircleNullDifference := MeasureEquivalenceCircleReduction.CircleNullRel

def CircleTailBound (a : CircleSequences) (N : ℕ) : Set CircleSequences :=
  {x | ∀ n, N ≤ n → ‖x n - a n‖ ≤ (1 / 8 : ℝ)}

theorem isClosed_circleTailBound (a : CircleSequences) (N : ℕ) :
    IsClosed (CircleTailBound a N) := by
  change IsClosed {x : CircleSequences | ∀ n, N ≤ n → ‖x n - a n‖ ≤ (1 / 8 : ℝ)}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro _hn
  exact isClosed_le (((continuous_apply n).sub continuous_const).norm) continuous_const

theorem interior_circleTailBound (a : CircleSequences) (N : ℕ) :
    interior (CircleTailBound a N) = ∅ := by
  apply eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp isOpen_interior x hx
  let n : ℕ := max N (I.sup id + 1)
  have hNn : N ≤ n := le_max_left _ _
  have hnI : n ∉ I := by
    intro hn
    have hle : n ≤ I.sup id := Finset.le_sup (f := id) hn
    have hlt : I.sup id < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
    omega
  let y : CircleSequences := Function.update x n (a n + ((1 / 2 : ℝ) : UnitAddCircle))
  have hy : y ∈ (I : Set ℕ).pi V := by
    intro i hi
    have hin : i ≠ n := by intro h; exact hnI (h ▸ hi)
    simpa only [y, Function.update_of_ne hin] using (hV i hi).2
  have hbad := interior_subset (hVI hy) n hNn
  have hnorm : ‖((1 / 2 : ℝ) : UnitAddCircle)‖ = (1 / 2 : ℝ) := by
    simpa using AddCircle.norm_half_period_eq (1 : ℝ)
  simp [y, hnorm] at hbad
  norm_num at hbad

theorem isNowhereDense_circleTailBound (a : CircleSequences) (N : ℕ) :
    IsNowhereDense (CircleTailBound a N) :=
  (isClosed_circleTailBound a N).isNowhereDense_iff.mpr (interior_circleTailBound a N)

/-- Every actual null-difference class in the compact circle product is meager. -/
theorem circleNullDifference_class_meagre (a : CircleSequences) :
    IsMeagre {x | CircleNullDifference x a} := by
  apply (isMeagre_iUnion (fun N => (isNowhereDense_circleTailBound a N).isMeagre)).mono
  intro x hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx (1 / 8 : ℝ) (by norm_num)
  exact mem_iUnion.2 ⟨N, fun n hn => by simpa only [dist_zero_right] using (hN n hn).le⟩

def FinitelySupportedCircle (h : CircleSequences) : Prop :=
  ∃ I : Finset ℕ, ∀ n, n ∉ I → h n = 0

theorem circleNullDifference_translate (h : CircleSequences)
    (hh : FinitelySupportedCircle h) (x : CircleSequences) :
    CircleNullDifference x (x + h) := by
  obtain ⟨I, hI⟩ := hh
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (I.sup id)] with n hn
  have hnI : n ∉ I := by
    intro hi
    exact (not_le_of_gt hn) (Finset.le_sup (f := id) hi)
  simp [hI n hnI]

/-- Finite-coordinate translations can move each point into any prescribed
nonempty product-open set. -/
theorem finite_translate_into_open (U : Set CircleSequences)
    (hU : IsOpen U) (hne : U.Nonempty) (x : CircleSequences) :
    ∃ h : CircleSequences, FinitelySupportedCircle h ∧ x + h ∈ U := by
  classical
  obtain ⟨u, hu⟩ := hne
  obtain ⟨I, V, hV, hVI⟩ := isOpen_pi_iff.mp hU u hu
  let h : CircleSequences := fun i => if i ∈ I then u i - x i else 0
  refine ⟨h, ⟨I, fun n hn => by simp [h, hn]⟩, hVI ?_⟩
  intro i hi
  change i ∈ I at hi
  simpa [h, hi] using (hV i hi).2

/-- Generic ergodicity of the concrete compact-circle null-difference
relation. A countable open subcover is extracted from finite-coordinate
translations; no unproved countability of the whole translating group is used. -/
theorem circleNullDifference_genericallyErgodic :
    GenericallyErgodic CircleNullDifference := by
  classical
  intro A hA hInv
  by_cases hm : IsMeagre A
  · exact Or.inl hm
  right
  obtain ⟨U, hUo, hAU⟩ := hA.residualEq_isOpen
  have hAU' : ∀ᶠ x in residual CircleSequences, x ∈ A ↔ x ∈ U :=
    Filter.eventuallyEq_set.mp hAU
  have hUne : U.Nonempty := by
    by_contra hn
    have hUe : U = ∅ := not_nonempty_iff_eq_empty.mp hn
    apply hm
    filter_upwards [hAU'] with x hx
    simp [hUe] at hx
    exact hx
  choose h hh hmem using finite_translate_into_open U hUo hUne
  let V : CircleSequences → Set CircleSequences := fun x => {y | y + h x ∈ U}
  have hVnhds (x : CircleSequences) : V x ∈ 𝓝 x :=
    (hUo.preimage (continuous_id.add continuous_const)).mem_nhds (hmem x)
  obtain ⟨S, hScount, hScover⟩ := TopologicalSpace.countable_cover_nhds hVnhds
  have hAll : ∀ᶠ y in residual CircleSequences, ∀ x ∈ S,
      y + h x ∈ A ↔ y + h x ∈ U := by
    apply eventually_countable_ball hScount |>.2
    intro x _hx
    exact tendsto_residual_of_isOpenMap
      (continuous_id.add continuous_const) (isOpenMap_add_right (h x)) hAU'
  filter_upwards [hAll] with y hy
  have hycover : y ∈ ⋃ x ∈ S, V x := by rw [hScover]; trivial
  obtain ⟨x, hx⟩ := mem_iUnion.1 hycover
  obtain ⟨hxS, hyV⟩ := mem_iUnion.1 hx
  have hyA : y + h x ∈ A := (hy x hxS).mpr hyV
  exact (hInv y (y + h x) (circleNullDifference_translate (h x) (hh x) y)).mpr hyA




end BenchmarkJump
end Source5
end BenchmarkJumpProof

/- Whole source module: FiniteFourier -/
namespace BenchmarkJumpProof
section Source6
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
end Source6
end BenchmarkJumpProof

/- Whole source module: ScalarMultiplier -/
namespace BenchmarkJumpProof
section Source7
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
end Source7
end BenchmarkJumpProof

/- Whole source module: TrigMultiplier -/
namespace BenchmarkJumpProof
section Source8
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
end Source8
end BenchmarkJumpProof

/- Whole source module: FiniteTorus -/
namespace BenchmarkJumpProof
section Source9
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
end Source9
end BenchmarkJumpProof

/- Whole source module: GridObstruction -/
namespace BenchmarkJumpProof
section Source10
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
end Source10
end BenchmarkJumpProof

/- Whole source module: CircleGrids -/
namespace BenchmarkJumpProof
section Source11
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
end Source11
end BenchmarkJumpProof

/- Whole source module: CircleTopology -/
namespace BenchmarkJumpProof
section Source12
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
end Source12
end BenchmarkJumpProof

/- Whole source module: CircleRowCover -/
namespace BenchmarkJumpProof
section Source13
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

abbrev NullCircleGroup := H0

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable
local instance : MeasurableSpace NullCircleGroup := borel NullCircleGroup
local instance : BorelSpace NullCircleGroup := ⟨rfl⟩
local instance : MeasurableSpace CircleSequences := borel CircleSequences
local instance : BorelSpace CircleSequences := ⟨rfl⟩

def nullCircleCoordinates (h : NullCircleGroup) : CircleSequences :=
  ((h : Hp ⊤) : CircleSequences)

theorem continuous_nullCircleCoordinates : Continuous nullCircleCoordinates :=
  continuous_h0_coordinates

def circleAction (p : CircleSequences × NullCircleGroup) : CircleSequences :=
  p.1 + nullCircleCoordinates p.2

theorem continuous_circleAction : Continuous circleAction :=
  continuous_fst.add (continuous_nullCircleCoordinates.comp continuous_snd)

/-- Endpoint maps of the actual circle null-group action are open. -/
theorem isOpenMap_circleAction : IsOpenMap circleAction := by
  intro W hW
  have heq : circleAction '' W = ⋃ h : NullCircleGroup,
      (fun x : CircleSequences => x + nullCircleCoordinates h) ''
        {x | (x, h) ∈ W} := by
    ext y
    constructor
    · rintro ⟨⟨x, h⟩, hxh, rfl⟩
      exact mem_iUnion.mpr ⟨h, x, hxh, rfl⟩
    · intro hy
      obtain ⟨h, x, hxh, hxy⟩ := mem_iUnion.mp hy
      exact ⟨(x, h), hxh, hxy⟩
  rw [heq]
  apply isOpen_iUnion
  intro h
  exact isOpenMap_add_right (nullCircleCoordinates h) _
    (hW.preimage (continuous_id.prodMk continuous_const))

theorem circleAction_null_related (p : CircleSequences × NullCircleGroup) :
    CircleNullDifference p.1 (circleAction p) := by
  have hh : Tendsto (fun n => nullCircleCoordinates p.2 n) atTop (𝓝 0) := p.2.property
  simpa [CircleNullDifference, MeasureEquivalenceCircleReduction.CircleNullRel,
    circleAction, nullCircleCoordinates] using hh.neg

/-- The concrete Baire cover step of the c0 jump proof: on one nonempty
rectangle a fixed output row matches a fixed input row with one uniform bound. -/
theorem circle_row_match_rectangle
    (F : CircleSequences → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism CircleNullDifference (Jump BoundedDifference) F)
    (k : ℕ) (A : Set CircleSequences) (hAo : IsOpen A) (hAn : A.Nonempty) :
    ∃ l n : ℕ, ∃ U : Set CircleSequences, ∃ W : Set NullCircleGroup,
      IsOpen U ∧ U.Nonempty ∧ IsOpen W ∧ W.Nonempty ∧
      U ×ˢ W ⊆ circleAction ⁻¹' A ∧
      ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
        p ∈ U ×ˢ W → UniformBound n (F (circleAction p) k) (F p.1 l) := by
  classical
  let B : ℕ × ℕ → Set (CircleSequences × NullCircleGroup) := fun i =>
    {p | UniformBound i.2 (F (circleAction p) k) (F p.1 i.1)}
  have hB (i : ℕ × ℕ) : BaireMeasurableSet (B i) := by
    apply MeasurableSet.baireMeasurableSet
    exact (isClosed_uniformBound i.2).measurableSet.preimage
      (((measurable_pi_apply k).comp (hFm.comp continuous_circleAction.measurable)).prodMk
        ((measurable_pi_apply i.1).comp (hFm.comp measurable_fst)))
  let Ω : Set (CircleSequences × NullCircleGroup) := circleAction ⁻¹' A
  have hΩo : IsOpen Ω := hAo.preimage continuous_circleAction
  have hΩn : Ω.Nonempty := by
    obtain ⟨x, hx⟩ := hAn
    refine ⟨(x, 0), ?_⟩
    have heq : circleAction (x, 0) = x := by
      ext n
      change x n + 0 = x n
      exact add_zero _
    change circleAction (x, 0) ∈ A
    rw [heq]
    exact hx
  have hCover : Ω ⊆ ⋃ i, B i := by
    intro p _hp
    obtain ⟨l, hl⟩ := (hF p.1 (circleAction p) (circleAction_null_related p)).2 k
    obtain ⟨n, hn⟩ := boundedDifference_equivalence.symm hl
    exact mem_iUnion.mpr ⟨(l, n), hn⟩
  obtain ⟨i, V, hVo, hVn, hVΩ, hVres⟩ :=
    baire_cover_local_residual B hB Ω hΩo hΩn hCover
  obtain ⟨⟨x, h⟩, hxh⟩ := hVn
  obtain ⟨U, W, hUo, hWo, hxU, hhW, hUW⟩ := isOpen_prod_iff.mp hVo x h hxh
  refine ⟨i.1, i.2, U, W, hUo, ⟨x, hxU⟩, hWo, ⟨h, hhW⟩,
    hUW.trans hVΩ, ?_⟩
  filter_upwards [hVres] with p hp hpUW
  exact hp (hUW hpUW)




end BenchmarkJump
end
end Source13
end BenchmarkJumpProof

/- Whole source module: CircleSmallPairs -/
namespace BenchmarkJumpProof
section Source14
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable

abbrev CircleTriples := CircleSequences × (NullCircleGroup × NullCircleGroup)

def tripleFirst (t : CircleTriples) : CircleSequences × NullCircleGroup :=
  (t.1, t.2.1)

def tripleSecond (t : CircleTriples) : CircleSequences × NullCircleGroup :=
  (t.1, t.2.2)

def tripleEndpoints (t : CircleTriples) : CircleSequences × CircleSequences :=
  (circleAction (tripleFirst t), circleAction (tripleSecond t))

theorem continuous_tripleFirst : Continuous tripleFirst :=
  continuous_fst.prodMk (continuous_fst.comp continuous_snd)

theorem continuous_tripleSecond : Continuous tripleSecond :=
  continuous_fst.prodMk (continuous_snd.comp continuous_snd)

theorem isOpenMap_tripleFirst : IsOpenMap tripleFirst :=
  IsOpenMap.id.prodMap isOpenMap_fst

theorem isOpenMap_tripleSecond : IsOpenMap tripleSecond :=
  IsOpenMap.id.prodMap isOpenMap_snd

theorem continuous_tripleEndpoints : Continuous tripleEndpoints :=
  (continuous_circleAction.comp continuous_tripleFirst).prodMk
    (continuous_circleAction.comp continuous_tripleSecond)

/-- The two row matches imply a uniform same-row bound for a comeager set
of triples, while both endpoints may additionally be required in D. -/
theorem circle_good_triples
    (U : Set CircleSequences) (W : Set NullCircleGroup) (D : Set CircleSequences)
    (hD : D ∈ residual CircleSequences) (f g : CircleSequences → RealSequences)
    (n : ℕ)
    (hRes : ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
      p ∈ U ×ˢ W → UniformBound n (f (circleAction p)) (g p.1)) :
    ∀ᶠ t in residual CircleTriples,
      t ∈ U ×ˢ (W ×ˢ W) →
        tripleEndpoints t ∈ D ×ˢ D ∧
        UniformBound (2 * n) (f (tripleEndpoints t).1) (f (tripleEndpoints t).2) := by
  have h1 := tendsto_residual_of_isOpenMap continuous_tripleFirst isOpenMap_tripleFirst hRes
  have h2 := tendsto_residual_of_isOpenMap continuous_tripleSecond isOpenMap_tripleSecond hRes
  have hD1 := tendsto_residual_of_isOpenMap
    (continuous_circleAction.comp continuous_tripleFirst)
    (isOpenMap_circleAction.comp isOpenMap_tripleFirst) hD
  have hD2 := tendsto_residual_of_isOpenMap
    (continuous_circleAction.comp continuous_tripleSecond)
    (isOpenMap_circleAction.comp isOpenMap_tripleSecond) hD
  filter_upwards [h1, h2, hD1, hD2] with t ht1 ht2 htD1 htD2 htRect
  refine ⟨⟨htD1, htD2⟩, ?_⟩
  have hB1 := ht1 ⟨htRect.1, htRect.2.1⟩
  have hB2 := ht2 ⟨htRect.1, htRect.2.2⟩
  have hB := uniformBound_trans hB1 (uniformBound_symm hB2)
  simpa only [two_mul] using hB

theorem mem_closure_inter_of_residual {T : Type*} [TopologicalSpace T] [BaireSpace T]
    (O G : Set T) (hOo : IsOpen O) (hG : G ∈ residual T) :
    O ⊆ closure (O ∩ G) := by
  intro x hx
  apply mem_closure_iff.mpr
  intro V hVo hxV
  obtain ⟨y, ⟨hyV, hyO⟩, hyG⟩ :=
    (dense_of_mem_residual hG).inter_open_nonempty (V ∩ O) (hVo.inter hOo) ⟨x, hxV, hx⟩
  exact ⟨y, hyV, hyO, hyG⟩

/-- Closed uniform output bounds extend along limits of pairs inside the
relative continuity set, exactly as used by the manuscript's closure step. -/
theorem uniformBound_of_mem_closure {D : Set CircleSequences}
    (f : CircleSequences → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ) (S : Set (CircleSequences × CircleSequences))
    (hSD : S ⊆ D ×ˢ D)
    (hBound : ∀ p ∈ S, UniformBound n (f p.1) (f p.2))
    (p : CircleSequences × CircleSequences) (hpD : p ∈ D ×ˢ D)
    (hp : p ∈ closure S) : UniformBound n (f p.1) (f p.2) := by
  have hc := ((hf p.1 hpD.1).prodMap (hf p.2 hpD.2)).mono hSD
  have hm : MapsTo (Prod.map f f) S
      {q : RealSequences × RealSequences | UniformBound n q.1 q.2} := hBound
  have hcl := hc.mem_closure hp hm
  simpa only [(isClosed_uniformBound n).closure_eq] using hcl

theorem norm_trunc0_le (s : Finset ℕ) (t : CircleSequences) (δ : ℝ)
    (hδ : 0 ≤ δ) (ht : ∀ i, ‖t i‖ ≤ δ) :
    ‖trunc0 s t‖ ≤ δ := by
  change ‖trunc ⊤ s t‖ ≤ δ
  apply lp.norm_le_of_forall_le hδ
  intro i
  rw [trunc_apply]
  split_ifs
  · exact ht i
  · simpa using hδ

theorem nullCircleCoordinates_add (h₁ h₂ : NullCircleGroup) :
    nullCircleCoordinates (h₁ + h₂) = nullCircleCoordinates h₁ + nullCircleCoordinates h₂ := rfl

theorem tendsto_truncated_endpoint (x y : CircleSequences) (h₀ : NullCircleGroup) :
    Tendsto
      (fun N : ℕ => circleAction
        (x, h₀ + trunc0 (Finset.range N) (y - circleAction (x, h₀))))
      atTop (𝓝 y) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop i] with N hN
  change y i = x i + (nullCircleCoordinates h₀ i +
    trunc ⊤ (Finset.range N) (y - circleAction (x, h₀)) i)
  rw [trunc_apply]
  simp only [Finset.mem_range, hN, ite_true, Pi.sub_apply, circleAction, Pi.add_apply,
    nullCircleCoordinates]
  abel





end BenchmarkJump
end
end Source14
end BenchmarkJumpProof

/- Whole source module: CircleRowClosure -/
namespace BenchmarkJumpProof
section Source15
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable

/-- The finite-truncation closure step in the concrete circle proof.
The uniform output bound holds even for a pair whose difference need not
itself be a null sequence, provided the coordinate distances are small. -/
theorem circle_small_pair_bound
    (U : Set CircleSequences) (W : Set NullCircleGroup)
    (hUo : IsOpen U) (hWo : IsOpen W)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f g : CircleSequences → RealSequences) (hf : ContinuousOn f D)
    (n : ℕ)
    (hRes : ∀ᶠ p in residual (CircleSequences × NullCircleGroup),
      p ∈ U ×ˢ W → UniformBound n (f (circleAction p)) (g p.1))
    (h₀ : NullCircleGroup) (hh₀ : h₀ ∈ W) (ε : ℝ)
    (hBall : Metric.ball h₀ ε ⊆ W)
    (x z : CircleSequences) (hx : x ∈ U)
    (hyD : circleAction (x, h₀) ∈ D) (hzD : z ∈ D)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδε : δ < ε)
    (hSmall : ∀ i, ‖z i - circleAction (x, h₀) i‖ ≤ δ) :
    UniformBound (2 * n) (f (circleAction (x, h₀))) (f z) := by
  classical
  let Ω : Set CircleTriples := U ×ˢ (W ×ˢ W)
  let G : Set CircleTriples := {t | t ∈ Ω →
    tripleEndpoints t ∈ D ×ˢ D ∧
    UniformBound (2 * n) (f (tripleEndpoints t).1) (f (tripleEndpoints t).2)}
  have hG : G ∈ residual CircleTriples := circle_good_triples U W D hD f g n hRes
  let S : Set CircleTriples := Ω ∩ G
  have hΩclosure : Ω ⊆ closure S :=
    mem_closure_inter_of_residual Ω G (hUo.prod (hWo.prod hWo)) hG
  let v : ℕ → CircleTriples := fun N =>
    (x, h₀, h₀ + trunc0 (Finset.range N) (z - circleAction (x, h₀)))
  have hv (N : ℕ) : v N ∈ Ω := by
    refine ⟨hx, hh₀, hBall ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have ht := norm_trunc0_le (Finset.range N) (z - circleAction (x, h₀)) δ hδ hSmall
    simpa only [v, add_sub_cancel_left] using lt_of_le_of_lt ht hδε
  have hvImg (N : ℕ) : tripleEndpoints (v N) ∈ closure (tripleEndpoints '' S) :=
    image_closure_subset_closure_image continuous_tripleEndpoints
      ⟨v N, hΩclosure (hv N), rfl⟩
  have hvLim : Tendsto (fun N => tripleEndpoints (v N)) atTop
      (𝓝 (circleAction (x, h₀), z)) :=
    tendsto_const_nhds.prodMk_nhds (tendsto_truncated_endpoint x z h₀)
  have hp : (circleAction (x, h₀), z) ∈ closure (tripleEndpoints '' S) :=
    isClosed_closure.mem_of_tendsto hvLim (Eventually.of_forall hvImg)
  apply uniformBound_of_mem_closure f hf (2 * n) (tripleEndpoints '' S)
    (fun p hp => ?_) (fun p hp => ?_) (circleAction (x, h₀), z) ⟨hyD, hzD⟩ hp
  · obtain ⟨t, ht, rfl⟩ := hp
    exact (ht.2 ht.1).1
  · obtain ⟨t, ht, rfl⟩ := hp
    exact (ht.2 ht.1).2



end BenchmarkJump
end
end Source15
end BenchmarkJumpProof

/- Whole source module: CircleChart -/
namespace BenchmarkJumpProof
section Source16
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

abbrev CircleChartInterval := Set.Ioo (0 : ℝ) 1
abbrev CircleChartSpace := ℕ → CircleChartInterval

def circleChartCoordinate (x : CircleChartInterval) : UnitAddCircle := (x : ℝ)

def circleChart (x : CircleChartSpace) : CircleSequences :=
  fun i => circleChartCoordinate (x i)

theorem isOpenEmbedding_circleChartCoordinate : IsOpenEmbedding circleChartCoordinate := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  · intro x y hxy
    apply Subtype.ext
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show (x : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from by
        simpa only [zero_add] using Ioo_subset_Ico_self x.property)
      (show (y : ℝ) ∈ Ico (0 : ℝ) (0 + 1) from by
        simpa only [zero_add] using Ioo_subset_Ico_self y.property)).mp
    exact hxy
  · exact QuotientAddGroup.isOpenMap_coe.comp isOpen_Ioo.isOpenMap_subtype_val

theorem isEmbedding_circleChart : IsEmbedding circleChart :=
  IsEmbedding.piMap (fun _ => isOpenEmbedding_circleChartCoordinate.isEmbedding)

theorem continuous_circleChart : Continuous circleChart := isEmbedding_circleChart.continuous

theorem range_circleChartCoordinate : range circleChartCoordinate = ({0}ᶜ : Set UnitAddCircle) := by
  have hr := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).image_source_eq_target
  convert hr using 1
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simpa [AddCircle.openPartialHomeomorphCoe, CircleChartInterval]
        using x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, by simpa [AddCircle.openPartialHomeomorphCoe, CircleChartInterval] using hx⟩, rfl⟩

theorem denseRange_circleChartCoordinate : DenseRange circleChartCoordinate := by
  intro y
  by_cases hy : y = 0
  · subst y
    have h0 : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact ⟨le_rfl, by norm_num⟩
    have hcl := image_closure_subset_closure_image (AddCircle.continuous_mk' (1 : ℝ))
      ⟨0, h0, rfl⟩
    have heq : ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (0 : ℝ) 1) =
        range circleChartCoordinate := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
    change (0 : UnitAddCircle) ∈ closure
      ((fun x : ℝ => (x : UnitAddCircle)) '' Set.Ioo (0 : ℝ) 1) at hcl
    rw [heq] at hcl
    exact hcl
  · apply subset_closure
    rw [range_circleChartCoordinate]
    simpa using hy

theorem denseRange_circleChart : DenseRange circleChart :=
  DenseRange.piMap (fun _ => denseRange_circleChartCoordinate)

theorem range_circleChart : range circleChart = {x : CircleSequences | ∀ i, x i ≠ 0} := by
  classical
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i
    have hi : circleChartCoordinate (y i) ∈ range circleChartCoordinate := mem_range_self _
    rw [range_circleChartCoordinate] at hi
    exact hi
  · intro hx
    have hi (i : ℕ) : ∃ y : CircleChartInterval, circleChartCoordinate y = x i := by
      apply mem_range.mp
      rw [range_circleChartCoordinate]
      exact hx i
    choose y hy using hi
    exact ⟨y, funext hy⟩

/-- The dense product chart is comeager in the compact circle product. -/
theorem circleChart_range_residual : range circleChart ∈ residual CircleSequences := by
  have hOne (i : ℕ) : {x : CircleSequences | x i ≠ 0} ∈ residual CircleSequences := by
    apply residual_of_dense_open
    · exact isOpen_compl_singleton.preimage (continuous_apply i)
    · have hd : Dense ({0}ᶜ : Set UnitAddCircle) := by
        rw [← range_circleChartCoordinate]
        exact denseRange_circleChartCoordinate
      exact hd.preimage (isOpenMap_eval i)
  simpa only [range_circleChart, setOf_forall] using countable_iInter_mem.mpr hOne

/-- Dense embeddings preserve residual assertions by preimage. -/
theorem tendsto_residual_of_denseEmbedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {f : A → B}
    (hf : IsEmbedding f) (hd : DenseRange f) : Tendsto f (residual A) (residual B) := by
  apply le_countableGenerate_iff_of_countableInterFilter.mpr
  rintro U ⟨hUo, hUd⟩
  apply residual_of_dense_open (hUo.preimage hf.continuous)
  apply dense_iff_inter_open.mpr
  intro V hVo hVn
  obtain ⟨W, hWo, hWV⟩ := hf.isInducing.isOpen_iff.mp hVo
  obtain ⟨a, haV⟩ := hVn
  have haW : f a ∈ W := by change a ∈ f ⁻¹' W; rw [hWV]; exact haV
  obtain ⟨b, hbW, hbU⟩ := hUd.inter_open_nonempty W hWo ⟨f a, haW⟩
  obtain ⟨z, hzWU, hzRange⟩ := hd.inter_open_nonempty (W ∩ U) (hWo.inter hUo) ⟨b, hbW, hbU⟩
  obtain ⟨a', rfl⟩ := hzRange
  exact ⟨a', by rw [← hWV]; exact hzWU.1, hzWU.2⟩




end BenchmarkJump
end
end Source16
end BenchmarkJumpProof

/- Whole source module: IntervalInterpolation -/
namespace BenchmarkJumpProof
section Source17
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

def affineMix (q : ℝ) (p : ℝ × ℝ) : ℝ := (1 - q) * p.1 + q * p.2

theorem continuous_affineMix (q : ℝ) : Continuous (affineMix q) := by
  unfold affineMix
  fun_prop

theorem isOpenMap_affineMix (q : ℝ) : IsOpenMap (affineMix q) := by
  by_cases hq : q = 1
  · subst q
    have heq : affineMix 1 = (@Prod.snd ℝ ℝ) := by
      funext p
      unfold affineMix
      ring
    rw [heq]
    exact isOpenMap_snd
  have hne : (1 - q : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  intro W hW
  have heq : affineMix q '' W = ⋃ y : ℝ,
      (fun x : ℝ => (1 - q) * x + q * y) '' {x | (x, y) ∈ W} := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact mem_iUnion.mpr ⟨y, x, hxy, rfl⟩
    · intro hz
      obtain ⟨y, x, hxy, hxz⟩ := mem_iUnion.mp hz
      exact ⟨(x, y), hxy, hxz⟩
  rw [heq]
  apply isOpen_iUnion
  intro y
  have hmul : IsOpenMap (fun x : ℝ => (1 - q) * x) := isOpenMap_smul₀ hne
  exact ((isOpenMap_add_right (q * y)).comp hmul) _
    (hW.preimage (continuous_id.prodMk continuous_const))

def intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : Set.Ioo a b × Set.Ioo a b) : Set.Ioo a b :=
  ⟨affineMix q (p.1, p.2), by
    simpa only [affineMix, smul_eq_mul] using
      (convex_Ioo a b) p.1.property p.2.property
        (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)⟩

theorem continuous_intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (intervalMix a b q hq0 hq1) :=
  ((continuous_affineMix q).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem isOpenMap_intervalMix (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (intervalMix a b q hq0 hq1) := by
  have hInc : IsOpenMap
      (fun p : Set.Ioo a b × Set.Ioo a b => ((p.1 : ℝ), (p.2 : ℝ))) :=
    isOpen_Ioo.isOpenMap_subtype_val.prodMap isOpen_Ioo.isOpenMap_subtype_val
  exact ((isOpenMap_affineMix q).comp hInc).subtype_mk _

theorem intervalMix_surjective (a b q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Function.Surjective (intervalMix a b q hq0 hq1) := by
  intro x
  refine ⟨(x, x), ?_⟩
  apply Subtype.ext
  change (1 - q) * (x : ℝ) + q * (x : ℝ) = (x : ℝ)
  ring

abbrev IntervalBox (a b : ℕ → ℝ) := ∀ i, Set.Ioo (a i) (b i)

def boxPairHomeomorph (a b : ℕ → ℝ) :
    (IntervalBox a b × IntervalBox a b) ≃ₜ
      (∀ i, Set.Ioo (a i) (b i) × Set.Ioo (a i) (b i)) where
  toFun p i := (p.1 i, p.2 i)
  invFun p := (fun i => (p i).1, fun i => (p i).2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)
  continuous_invFun :=
    (continuous_pi fun i => continuous_fst.comp (continuous_apply i)).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

def boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : IntervalBox a b × IntervalBox a b) : IntervalBox a b :=
  fun i => intervalMix (a i) (b i) q hq0 hq1 (p.1 i, p.2 i)

theorem continuous_boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (boxMix a b q hq0 hq1) :=
  (continuous_pi fun i => (continuous_intervalMix (a i) (b i) q hq0 hq1).comp
    (((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)))

theorem isOpenMap_boxMix (a b : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (boxMix a b q hq0 hq1) :=
  (IsOpenMap.piMap
    (fun i => isOpenMap_intervalMix (a i) (b i) q hq0 hq1)
    (Eventually.of_forall fun i => intervalMix_surjective (a i) (b i) q hq0 hq1)).comp
      (boxPairHomeomorph a b).isOpenMap

theorem affineMix_difference (x y q r : ℝ) :
    |affineMix q (x, y) - affineMix r (x, y)| = |q - r| * |y - x| := by
  have heq : affineMix q (x, y) - affineMix r (x, y) = (q - r) * (y - x) := by
    unfold affineMix
    ring
  rw [heq, abs_mul]

/-- The uniform coordinate estimate for interpolation in a bounded chart. -/
theorem circle_affineMix_bound (x y q r : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ‖(affineMix q (x, y) : UnitAddCircle) -
      (affineMix r (x, y) : UnitAddCircle)‖ ≤ |q - r| := by
  have hxy : |y - x| ≤ (1 : ℝ) := abs_le.mpr ⟨by linarith [hy.1, hx.2],
    by linarith [hy.2, hx.1]⟩
  calc
    _ = ‖((affineMix q (x, y) - affineMix r (x, y) : ℝ) : UnitAddCircle)‖ := by
      rw [AddCircle.coe_sub]
    _ ≤ |affineMix q (x, y) - affineMix r (x, y)| := by
      simpa only [Real.norm_eq_abs] using
        (QuotientAddGroup.norm_mk_le_norm
          (m := affineMix q (x, y) - affineMix r (x, y))
          (S := AddSubgroup.zmultiples (1 : ℝ)))
    _ = |q - r| * |y - x| := affineMix_difference x y q r
    _ ≤ |q - r| * 1 := mul_le_mul_of_nonneg_left hxy (abs_nonneg _)
    _ = |q - r| := mul_one _




end BenchmarkJump
end
end Source17
end BenchmarkJumpProof

/- Whole source module: ChartConvexNeighborhood -/
namespace BenchmarkJumpProof
section Source18
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

def chartMix (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (p : CircleChartSpace × CircleChartSpace) : CircleChartSpace :=
  boxMix (fun _ => 0) (fun _ => 1) q hq0 hq1 p

theorem continuous_chartMix (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (chartMix q hq0 hq1) :=
  continuous_boxMix (fun _ => 0) (fun _ => 1) q hq0 hq1

theorem isOpenMap_chartMix (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (chartMix q hq0 hq1) :=
  isOpenMap_boxMix (fun _ => 0) (fun _ => 1) q hq0 hq1

def ChartConvex (C : Set CircleChartSpace) : Prop :=
  ∀ q (hq0 : 0 ≤ q) (hq1 : q ≤ 1), ∀ x ∈ C, ∀ y ∈ C,
    chartMix q hq0 hq1 (x, y) ∈ C

/-- Every nonempty open set in the product chart contains a nonempty open
cylinder preserved by all coordinatewise affine interpolations. -/
theorem exists_open_chartConvex_subset (V : Set CircleChartSpace)
    (hVo : IsOpen V) (hVn : V.Nonempty) :
    ∃ C : Set CircleChartSpace, IsOpen C ∧ C.Nonempty ∧ C ⊆ V ∧ ChartConvex C := by
  classical
  obtain ⟨x, hx⟩ := hVn
  obtain ⟨I, U, hU, hUV⟩ := isOpen_pi_iff.mp hVo x hx
  have hB (i : ℕ) (hi : i ∈ I) :
      ∃ ε > (0 : ℝ), Metric.ball (x i) ε ⊆ U i :=
    Metric.isOpen_iff.mp (hU i hi).1 (x i) (hU i hi).2
  choose ε hεpos hεsub using hB
  let r : ℕ → ℝ := fun i => if hi : i ∈ I then ε i hi else 1
  let C : Set CircleChartSpace := (I : Set ℕ).pi fun i => Metric.ball (x i) (r i)
  have hCr (i : ℕ) (hi : i ∈ I) : 0 < r i := by
    simpa [r, hi] using hεpos i hi
  refine ⟨C, isOpen_set_pi I.finite_toSet (fun _ _ => Metric.isOpen_ball), ?_, ?_, ?_⟩
  · refine ⟨x, ?_⟩
    intro i hi
    exact Metric.mem_ball_self (hCr i hi)
  · intro y hy
    apply hUV
    intro i hi
    change i ∈ I at hi
    apply hεsub i hi
    simpa [r, hi] using hy i hi
  · intro q hq0 hq1 y hy z hz
    intro i hi
    have hyD : |(y i : ℝ) - (x i : ℝ)| < r i := hy i hi
    have hzD : |(z i : ℝ) - (x i : ℝ)| < r i := hz i hi
    have hyR : (y i : ℝ) ∈ Set.Ioo ((x i : ℝ) - r i) ((x i : ℝ) + r i) :=
      ⟨by linarith [(abs_lt.mp hyD).1], by linarith [(abs_lt.mp hyD).2]⟩
    have hzR : (z i : ℝ) ∈ Set.Ioo ((x i : ℝ) - r i) ((x i : ℝ) + r i) :=
      ⟨by linarith [(abs_lt.mp hzD).1], by linarith [(abs_lt.mp hzD).2]⟩
    have hmix := (convex_Ioo ((x i : ℝ) - r i) ((x i : ℝ) + r i)) hyR hzR
      (sub_nonneg.mpr hq1) hq0 (by ring : 1 - q + q = 1)
    change (x i : ℝ) - r i < affineMix q ((y i : ℝ), (z i : ℝ)) ∧
      affineMix q ((y i : ℝ), (z i : ℝ)) < (x i : ℝ) + r i at hmix
    change |affineMix q ((y i : ℝ), (z i : ℝ)) - (x i : ℝ)| < r i
    apply abs_lt.mpr
    constructor <;> linarith [hmix.1, hmix.2]

def chartMixOn (C : Set CircleChartSpace) (hC : ChartConvex C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (p : C × C) : C :=
  ⟨chartMix q hq0 hq1 (p.1, p.2), hC q hq0 hq1 p.1 p.1.property p.2 p.2.property⟩

theorem continuous_chartMixOn (C : Set CircleChartSpace) (hC : ChartConvex C)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Continuous (chartMixOn C hC q hq0 hq1) :=
  ((continuous_chartMix q hq0 hq1).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _

theorem isOpenMap_chartMixOn (C : Set CircleChartSpace) (hCo : IsOpen C)
    (hC : ChartConvex C) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsOpenMap (chartMixOn C hC q hq0 hq1) :=
  ((isOpenMap_chartMix q hq0 hq1).comp
    (hCo.isOpenMap_subtype_val.prodMap hCo.isOpenMap_subtype_val)).subtype_mk _




end BenchmarkJump
end
end Source18
end BenchmarkJumpProof

/- Whole source module: CircleChartConstancy -/
namespace BenchmarkJumpProof
section Source19
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- Constancy on a comeager part of a nonempty open chart set transfers
to constancy on a comeager part of a nonempty ambient open set. -/
theorem circleChart_local_constancy
    (A : Set CircleSequences) (hAo : IsOpen A)
    (C : Set CircleChartSpace) (hCo : IsOpen C) (hCn : C.Nonempty)
    (hCA : C ⊆ circleChart ⁻¹' A) (P : CircleSequences → Prop)
    (hP : ∀ᶠ x : C in residual C, P (circleChart x)) :
    ∃ O : Set CircleSequences, IsOpen O ∧ O.Nonempty ∧ O ⊆ A ∧
      ∀ᶠ y in residual CircleSequences, y ∈ O → P y := by
  classical
  obtain ⟨V, hVo, hVC⟩ := isEmbedding_circleChart.isInducing.isOpen_iff.mp hCo
  let O : Set CircleSequences := V ∩ A
  have hOn : O.Nonempty := by
    obtain ⟨x, hx⟩ := hCn
    exact ⟨circleChart x, by change x ∈ circleChart ⁻¹' V; rw [hVC]; exact hx, hCA hx⟩
  have hm : IsMeagre {x : C | ¬ P (circleChart x)} := by
    simpa only [IsMeagre, compl_setOf, not_not] using hP
  have hImage : IsMeagre
      ((fun x : C => circleChart x) '' {x : C | ¬ P (circleChart x)}) :=
    (isEmbedding_circleChart.isInducing.comp IsInducing.subtypeVal).isMeagre_image hm
  refine ⟨O, hVo.inter hAo, hOn, inter_subset_right, ?_⟩
  filter_upwards [circleChart_range_residual, hImage] with y hyRange hyBad hyO
  obtain ⟨x, rfl⟩ := hyRange
  have hxC : x ∈ C := by
    rw [← hVC]
    exact hyO.1
  by_contra hxP
  exact hyBad ⟨⟨x, hxC⟩, hxP, rfl⟩

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
end Source19
end BenchmarkJumpProof

/- Whole source module: CircleInterpolationChain -/
namespace BenchmarkJumpProof
section Source20
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

/-- Affine interpolation turns the small-pair bound into generic row
constancy on an actual open cylinder of the product circle chart. -/
theorem circle_interpolation_generic_pairs
    (C : Set CircleChartSpace) (hCo : IsOpen C) (hC : ChartConvex C)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f : CircleSequences → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ circleChart '' C, ∀ z ∈ circleChart '' C,
      y ∈ D → z ∈ D → ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      (∀ i, ‖z i - y i‖ ≤ δ) → BoundedDifference (f y) (f z)) :
    ∀ᶠ p : C × C in residual (C × C),
      BoundedDifference (f (circleChart p.1)) (f (circleChart p.2)) := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hε
  let m : ℕ := M + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hdiv : 1 / (m : ℝ) < ε := by exact_mod_cast hM
  let P (j : Fin (m + 1)) : C × C → C := chartMixOn C hC (chainParameter m hm j)
    (chainParameter_nonneg m hm j) (chainParameter_le_one m hm j)
  have hDC : ∀ᶠ x : C in residual C, circleChart x ∈ D :=
    eventually_residual_open_subspace C hCo
      (tendsto_residual_of_denseEmbedding isEmbedding_circleChart denseRange_circleChart hD)
  have hAll : ∀ᶠ p : C × C in residual (C × C),
      ∀ j : Fin (m + 1), circleChart (P j p) ∈ D := by
    apply eventually_countable_forall.mpr
    intro j
    exact tendsto_residual_of_isOpenMap
      (continuous_chartMixOn C hC _ _ _) (isOpenMap_chartMixOn C hCo hC _ _ _) hDC
  filter_upwards [hAll] with p hp
  let u : Fin (m + 1) → RealSequences := fun j => f (circleChart (P j p))
  have hStep (j : Fin m) : BoundedDifference (u j.castSucc) (u j.succ) := by
    apply hSmall (circleChart (P j.castSucc p))
      ⟨P j.castSucc p, (P j.castSucc p).property, rfl⟩
      (circleChart (P j.succ p)) ⟨P j.succ p, (P j.succ p).property, rfl⟩
      (hp j.castSucc) (hp j.succ) (1 / (m : ℝ)) (by positivity) hdiv
    intro i
    have hnorm := circle_affineMix_bound ((p.1 : CircleChartSpace) i : ℝ)
      ((p.2 : CircleChartSpace) i : ℝ)
      (chainParameter m hm j.succ) (chainParameter m hm j.castSucc)
      ⟨((p.1 : CircleChartSpace) i).property.1.le,
        ((p.1 : CircleChartSpace) i).property.2.le⟩
      ⟨((p.2 : CircleChartSpace) i).property.1.le,
        ((p.2 : CircleChartSpace) i).property.2.le⟩
    rw [abs_sub_comm, chainParameter_step m hm j] at hnorm
    exact hnorm
  have hP0 : P 0 p = p.1 := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change affineMix (chainParameter m hm 0)
      (((p.1 : CircleChartSpace) i : ℝ), ((p.2 : CircleChartSpace) i : ℝ)) = _
    simp only [chainParameter, Fin.val_zero, Nat.cast_zero, zero_div, affineMix]
    ring
  have hP1 : P (Fin.last m) p = p.2 := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change affineMix (chainParameter m hm (Fin.last m))
      (((p.1 : CircleChartSpace) i : ℝ), ((p.2 : CircleChartSpace) i : ℝ)) = _
    simp only [chainParameter, Fin.val_last, div_self hm0, affineMix]
    ring
  have hChain := boundedDifference_fin_chain m u hStep
  change BoundedDifference (f (circleChart (P 0 p)))
    (f (circleChart (P (Fin.last m) p))) at hChain
  rwa [hP0, hP1] at hChain

theorem circle_interpolation_constant_on_chart
    (C : Set CircleChartSpace) (hCo : IsOpen C) (hCn : C.Nonempty) (hC : ChartConvex C)
    (D : Set CircleSequences) (hD : D ∈ residual CircleSequences)
    (f : CircleSequences → RealSequences) (ε : ℝ) (hε : 0 < ε)
    (hSmall : ∀ y ∈ circleChart '' C, ∀ z ∈ circleChart '' C,
      y ∈ D → z ∈ D → ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      (∀ i, ‖z i - y i‖ ≤ δ) → BoundedDifference (f y) (f z)) :
    ∃ a : RealSequences, ∀ᶠ x : C in residual C, BoundedDifference (f (circleChart x)) a := by
  letI : PolishSpace CircleChartInterval := isOpen_Ioo.polishSpace
  letI : Nonempty C := hCn.to_subtype
  letI : BaireSpace C := hCo.baireSpace
  have hPair := circle_interpolation_generic_pairs C hCo hC D hD f ε hε hSmall
  obtain ⟨x, hx⟩ := exists_residual_section hPair
  refine ⟨f (circleChart x), ?_⟩
  filter_upwards [hx] with y hy
  exact boundedDifference_equivalence.symm hy



end BenchmarkJump
end
end Source20
end BenchmarkJumpProof

/- Whole source module: CircleJumpObstruction -/
namespace BenchmarkJumpProof
section Source21
open Filter Set Topology TopologicalSpace
open scoped Topology

noncomputable section

namespace BenchmarkJump

open MeasureEquivalenceCircle MeasureEquivalenceCircleTopology

local instance : PolishSpace NullCircleGroup := h0_polish
local instance : SeparableSpace NullCircleGroup := h0_separable
local instance : MeasurableSpace NullCircleGroup := borel NullCircleGroup
local instance : BorelSpace NullCircleGroup := ⟨rfl⟩
local instance : MeasurableSpace CircleSequences := borel CircleSequences
local instance : BorelSpace CircleSequences := ⟨rfl⟩

/-- The actual local row property for every Borel jump homomorphism out of
compact-circle null difference. All analytic and category hypotheses are
discharged by the preceding modules. -/
theorem circle_local_rows
    (F : CircleSequences → ℕ → RealSequences) (hFm : Measurable F)
    (hF : Homomorphism CircleNullDifference (Jump BoundedDifference) F) :
    LocallyGenericallyConstantRows BoundedDifference F := by
  intro k A hAo hAn
  obtain ⟨l, n, U, W, hUo, hUn, hWo, hWn, hRect, hRes⟩ :=
    circle_row_match_rectangle F hFm hF k A hAo hAn
  obtain ⟨h₀, hh₀⟩ := hWn
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hWo h₀ hh₀
  let f : CircleSequences → RealSequences := fun x => F x k
  let g : CircleSequences → RealSequences := fun x => F x l
  obtain ⟨D, hDG, _hDd, hf⟩ := measurable_continuousOn_residual f
    ((measurable_pi_apply k).comp hFm)
  have hD : D ∈ residual CircleSequences := residual_of_dense_Gδ hDG _hDd
  let Ω : Set CircleSequences :=
    (fun x : CircleSequences => x + nullCircleCoordinates h₀) '' U
  have hΩo : IsOpen Ω := isOpenMap_add_right (nullCircleCoordinates h₀) _ hUo
  have hΩn : Ω.Nonempty := hUn.image _
  have hΩA : Ω ⊆ A := by
    rintro y ⟨x, hxU, rfl⟩
    exact hRect (show (x, h₀) ∈ U ×ˢ W from ⟨hxU, hh₀⟩)
  have hVn : (circleChart ⁻¹' Ω).Nonempty := by
    obtain ⟨y, hyΩ, hyRange⟩ := denseRange_circleChart.inter_open_nonempty Ω hΩo hΩn
    obtain ⟨x, rfl⟩ := hyRange
    exact ⟨x, hyΩ⟩
  obtain ⟨C, hCo, hCn, hCV, hC⟩ := exists_open_chartConvex_subset
    (circleChart ⁻¹' Ω) (hΩo.preimage continuous_circleChart) hVn
  have hSmall : ∀ y ∈ circleChart '' C, ∀ z ∈ circleChart '' C,
      y ∈ D → z ∈ D → ∀ δ : ℝ, 0 ≤ δ → δ < ε →
      (∀ i, ‖z i - y i‖ ≤ δ) → BoundedDifference (f y) (f z) := by
    intro y hyC z _hzC hyD hzD δ hδ hδε hSmall
    have hyΩ : y ∈ Ω := by
      obtain ⟨cy, hcy, rfl⟩ := hyC
      exact hCV hcy
    obtain ⟨x, hxU, hxy⟩ := hyΩ
    have hxy' : circleAction (x, h₀) = y := hxy
    refine ⟨2 * n, ?_⟩
    have hb := circle_small_pair_bound U W hUo hWo D hD f g hf n hRes
      h₀ hh₀ ε hBall x z hxU (hxy'.symm ▸ hyD) hzD δ hδ hδε
      (fun i => by simpa only [hxy'] using hSmall i)
    simpa only [hxy'] using hb
  obtain ⟨a, ha⟩ := circle_interpolation_constant_on_chart C hCo hCn hC D hD f ε hε hSmall
  obtain ⟨O, hOo, hOn, hOA, hConst⟩ := circleChart_local_constancy A hAo C hCo hCn
    (fun x hx => hΩA (hCV hx)) (fun y => BoundedDifference (f y) a) ha
  exact ⟨O, a, hOo, hOn, hOA, hConst⟩

/-- No Borel reduction of actual compact-circle null difference to the
Friedman--Stanley jump of actual bounded difference exists. -/
theorem circle_null_not_borel_reducible_to_jump :
    ¬ ∃ F : CircleSequences → ℕ → RealSequences, Measurable F ∧
      ∀ x y, CircleNullDifference x y ↔ Jump BoundedDifference (F x) (F y) :=
  not_borel_reduction_of_local_rows CircleNullDifference BoundedDifference
    boundedDifference_equivalence measurableSet_boundedDifference
    circleNullDifference_genericallyErgodic circleNullDifference_class_meagre
    circle_local_rows

/-- The c0 half of Theorem1.4: the usual real null-difference relation is
not Borel reducible to the Friedman--Stanley jump of bounded difference. -/
theorem c0_not_borel_reducible_to_boundedDifferenceJump :
    ¬ ∃ F : RealSequences → ℕ → RealSequences, Measurable F ∧
      ∀ x y, Tendsto (fun i => x i - y i) atTop (𝓝 0) ↔
        Jump BoundedDifference (F x) (F y) := by
  rintro ⟨F, hFm, hRed⟩
  apply circle_null_not_borel_reducible_to_jump
  refine ⟨F ∘ MeasureEquivalenceCircleReduction.realEmbed,
    hFm.comp MeasureEquivalenceCircleReduction.continuous_realEmbed.measurable, ?_⟩
  intro x y
  exact (MeasureEquivalenceCircleReduction.circle_real_null_reduction x y).trans
    (hRed (MeasureEquivalenceCircleReduction.realEmbed x)
      (MeasureEquivalenceCircleReduction.realEmbed y))





end BenchmarkJump
end
end Source21
end BenchmarkJumpProof

/- Whole source module: BenchmarkJumpBridge -/
namespace BenchmarkJumpProof
section Source22
open _root_.BenchmarkComparisons
/-! Bridge from the verified obstruction to the exact mission definitions.
Only the c0 half of the paired jump statement is claimed here. -/

namespace BenchmarkComparisons

theorem c0_jump_obstruction :
    ¬ BorelReduces NullDifference (Jump BoundedDifference) := by
  rintro ⟨F, hFm, hRed⟩
  apply BenchmarkJump.c0_not_borel_reducible_to_boundedDifferenceJump
  refine ⟨F, hFm, ?_⟩
  intro x y
  apply (hRed x y).trans
  simp only [Jump, BenchmarkJump.Jump, BoundedDifference,
    ← BenchmarkJump.boundedDifference_iff_real_bound]



end BenchmarkComparisons
end Source22
end BenchmarkJumpProof

theorem solution : ¬ BenchmarkComparisons.BorelReduces BenchmarkComparisons.NullDifference (BenchmarkComparisons.Jump BenchmarkComparisons.BoundedDifference) := by
  exact BenchmarkJumpProof.BenchmarkComparisons.c0_jump_obstruction

#print axioms solution
