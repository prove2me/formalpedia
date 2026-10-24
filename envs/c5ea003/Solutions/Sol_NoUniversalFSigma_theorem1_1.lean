-- Prove2me | solution 1 for NoUniversalFSigma.theorem1_1
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-23T09:26:10.974765+00:00
-- url     : https://prove2.me/submissions/b35ce293-8585-40b3-b841-66e35f81520c

import Definitions.Def_NoUniversalFSigma261031052
import Mathlib.SetTheory.Ordinal.FixedPointApproximants
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Tactic.Push
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.SetTheory.Ordinal.FundamentalSequence
import Mathlib.Topology.Sequences
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/- Source module: NoUniversalFSigma.TargetRank -/
section
open Set TopologicalSpace
open scoped Cardinal Ordinal

namespace NoUniversalFSigma

noncomputable section

universe u
variable {X : Type u}

/-- The transfinite iteration of a monotone removal operation. -/
def derivativeIter (D : Set X →o Set X) (A : Set X) (ξ : Ordinal.{u}) : Set X :=
  OrdinalApprox.gfpApprox D A ξ

@[simp] theorem derivativeIter_zero (D : Set X →o Set X) (A : Set X) :
    derivativeIter D A 0 = A := OrdinalApprox.gfpApprox_zero D

theorem derivativeIter_antitone (D : Set X →o Set X) (A : Set X) :
    Antitone (derivativeIter D A) := OrdinalApprox.gfpApprox_anti_right D

theorem derivativeIter_subset (D : Set X →o Set X) (A : Set X) (ξ : Ordinal.{u}) :
    derivativeIter D A ξ ⊆ A := OrdinalApprox.gfpApprox_le D

@[simp] theorem derivativeIter_succ (D : Set X →o Set X) (A : Set X)
    (hD : ∀ B, D B ⊆ B) (ξ : Ordinal.{u}) :
    derivativeIter D A (ξ + 1) = D (derivativeIter D A ξ) :=
  OrdinalApprox.gfpApprox_add_one D (hD A) ξ

theorem derivativeIter_limit (D : Set X →o Set X) (A : Set X)
    {ξ : Ordinal.{u}} (hξ : Order.IsSuccLimit ξ) :
    derivativeIter D A ξ = ⋂ η : Set.Iio ξ, derivativeIter D A η :=
  OrdinalApprox.gfpApprox_of_isSuccLimit D hξ

variable [TopologicalSpace X]

/-- Points of `A` where no relative neighborhood is contained in a single member
of the cover. This is the relative unboundedness derivative used for the target rank. -/
def coverDerivative (C : ℕ → Set X) : Set X →o Set X where
  toFun A := A ∩ ⋂ k, closure (A \ C k)
  monotone' := by
    intro A B hAB
    exact inter_subset_inter hAB (iInter_mono fun k => closure_mono (diff_subset_diff_left hAB))

theorem coverDerivative_subset (C : ℕ → Set X) (A : Set X) :
    coverDerivative C A ⊆ A := inter_subset_left

theorem isClosed_coverDerivative (C : ℕ → Set X) {A : Set X} (hA : IsClosed A) :
    IsClosed (coverDerivative C A) :=
  hA.inter (isClosed_iInter fun _ => isClosed_closure)

theorem isClosed_derivativeIter (D : Set X →o Set X)
    (hD : ∀ A, IsClosed A → IsClosed (D A)) {A : Set X} (hA : IsClosed A)
    (ξ : Ordinal.{u}) : IsClosed (derivativeIter D A ξ) := by
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
    change IsClosed (OrdinalApprox.gfpApprox D A ξ)
    rw [OrdinalApprox.gfpApprox]
    exact hA.inter (isClosed_iInter fun η => isClosed_iInter fun hη => hD _ (IH η hη))

end
end NoUniversalFSigma

namespace NoUniversalFSigma
noncomputable section
universe u
open Set TopologicalSpace Ordinal
open scoped Cardinal
variable {X : Type u} [TopologicalSpace X]

/-- Closed countable covers remove a point from every nonempty closed set. -/
theorem coverDerivative_ne_self [PolishSpace X] (C : ℕ → Set X)
    (hC : ∀ k, IsClosed (C k)) (hcover : ⋃ k, C k = Set.univ)
    {A : Set X} (hA : IsClosed A) (hne : A.Nonempty) :
    coverDerivative C A ≠ A := by
  letI : PolishSpace A := hA.polishSpace
  letI : Nonempty A := hne.to_subtype
  let C' : ℕ → Set A := fun k => Subtype.val ⁻¹' C k
  have hC' : ∀ k, IsClosed (C' k) := fun k => (hC k).preimage continuous_subtype_val
  have hc' : ⋃ k, C' k = Set.univ := by
    ext x
    simp only [C', ← preimage_iUnion, hcover, preimage_univ]
  obtain ⟨x, hx⟩ := (dense_iUnion_interior_of_closed hC' hc').nonempty
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  have himage : Subtype.val '' (C' k)ᶜ = A \ C k := by
    ext y
    simp only [mem_image, mem_compl_iff, C', mem_preimage, mem_diff]
    exact ⟨fun ⟨z, hz, hzy⟩ => hzy ▸ ⟨z.property, hz⟩,
      fun hy => ⟨⟨y, hy.1⟩, hy.2, rfl⟩⟩
  intro heq
  have hclosure : x.val ∈ closure (A \ C k) := by
    have hxD : x.val ∈ coverDerivative C A := heq.symm ▸ x.property
    exact mem_iInter.mp hxD.2 k
  have hxcl : x ∈ closure (C' k)ᶜ := closure_subtype.mpr (himage ▸ hclosure)
  rw [closure_compl] at hxcl
  exact hxcl hk

/-- A decreasing closed derivative stabilizes at a countable stage in a second
countable space. The proof extracts a countable subunion of the open complements. -/
theorem derivativeIter_exists_countable_fixed [SecondCountableTopology X]
    (D : Set X →o Set X) (hD : ∀ A, D A ⊆ A)
    (hclosed : ∀ A, IsClosed A → IsClosed (D A))
    {A : Set X} (hA : IsClosed A) :
    ∃ ξ : Ordinal.{u}, ξ < ω₁ ∧ D (derivativeIter D A ξ) = derivativeIter D A ξ := by
  let J := Set.Iio (ω₁ : Ordinal.{u})
  let U : J → Set X := fun ξ => (derivativeIter D A ξ.val)ᶜ
  have hU : ∀ ξ, IsOpen (U ξ) :=
    fun ξ => (isClosed_derivativeIter D hclosed hA ξ.val).isOpen_compl
  obtain ⟨T, hT, hTU⟩ := isOpen_iUnion_countable U hU
  letI : Countable T := hT.to_subtype
  let ξ : Ordinal.{u} := ⨆ η : T, η.val.val
  have hξ : ξ < ω₁ := Ordinal.iSup_lt_omega_one fun η => η.val.property
  have hsub : ∀ η : J, derivativeIter D A ξ ⊆ derivativeIter D A η.val := by
    intro η x hx
    by_contra hxη
    have hxU : x ∈ ⋃ η : J, U η := mem_iUnion.mpr ⟨η, hxη⟩
    rw [← hTU] at hxU
    obtain ⟨β, hβ⟩ := mem_iUnion.mp hxU
    obtain ⟨hβT, hxβ⟩ := mem_iUnion.mp hβ
    have hβξ : β.val ≤ ξ := Ordinal.le_iSup (fun η : T => η.val.val) ⟨β, hβT⟩
    exact hxβ (derivativeIter_antitone D A hβξ hx)
  refine ⟨ξ, hξ, (hD _).antisymm ?_⟩
  rw [← derivativeIter_succ D A hD ξ]
  exact hsub ⟨ξ + 1, (Cardinal.isSuccLimit_omega 1).add_one_lt hξ⟩

/-- A closed derivative which strictly decreases every nonempty closed set becomes
empty at a countable ordinal. -/
theorem derivativeIter_exists_countable_empty [SecondCountableTopology X]
    (D : Set X →o Set X) (hD : ∀ A, D A ⊆ A)
    (hclosed : ∀ A, IsClosed A → IsClosed (D A))
    (hstrict : ∀ A, IsClosed A → A.Nonempty → D A ≠ A)
    {A : Set X} (hA : IsClosed A) :
    ∃ ξ : Ordinal.{u}, ξ < ω₁ ∧ derivativeIter D A ξ = ∅ := by
  obtain ⟨ξ, hξ, hfix⟩ := derivativeIter_exists_countable_fixed D hD hclosed hA
  refine ⟨ξ, hξ, ?_⟩
  by_contra hne
  exact hstrict _ (isClosed_derivativeIter D hclosed hA ξ) (Set.nonempty_iff_ne_empty.mpr hne) hfix

/-- The rank of a countable closed cover of a Polish space is countable. -/
theorem coverDerivative_exists_countable_empty [PolishSpace X] (C : ℕ → Set X)
    (hC : ∀ k, IsClosed (C k)) (hcover : ⋃ k, C k = Set.univ)
    {A : Set X} (hA : IsClosed A) :
    ∃ ξ : Ordinal.{u}, ξ < ω₁ ∧ derivativeIter (coverDerivative C) A ξ = ∅ := by
  exact derivativeIter_exists_countable_empty (coverDerivative C)
    (coverDerivative_subset C) (fun _ => isClosed_coverDerivative C)
    (fun _ => coverDerivative_ne_self C hC hcover) hA

end
end NoUniversalFSigma



namespace NoUniversalFSigma
noncomputable section
universe u
open Set TopologicalSpace Ordinal
variable {Y : Type u} [TopologicalSpace Y]

/-- The closed space of pairs of composable arrows in the `n`th approximation. -/
def targetTripleSet (C : ℕ → Set (Y × Y)) (n : ℕ) : Set (Y × Y × Y) :=
  {t | (t.1, t.2.1) ∈ C n ∧ (t.2.1, t.2.2) ∈ C n}

/-- The `k`th closed endpoint-composition sublevel set. No minimum function is needed. -/
def targetLevelSet (C : ℕ → Set (Y × Y)) (n k : ℕ) : Set (targetTripleSet C n) :=
  {t | (t.val.1, t.val.2.2) ∈ C k}

def targetDerivative (C : ℕ → Set (Y × Y)) (n : ℕ) :
    Set (targetTripleSet C n) →o Set (targetTripleSet C n) :=
  coverDerivative (targetLevelSet C n)

def targetIter (C : ℕ → Set (Y × Y)) (n : ℕ) (ξ : Ordinal.{u}) :
    Set (targetTripleSet C n) :=
  derivativeIter (targetDerivative C n) Set.univ ξ

theorem isClosed_targetTripleSet (C : ℕ → Set (Y × Y))
    (hC : ∀ n, IsClosed (C n)) (n : ℕ) : IsClosed (targetTripleSet C n) := by
  exact ((hC n).preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).inter
    ((hC n).preimage ((continuous_fst.comp continuous_snd).prodMk
      (continuous_snd.comp continuous_snd)))

theorem isClosed_targetLevelSet (C : ℕ → Set (Y × Y))
    (hC : ∀ n, IsClosed (C n)) (n k : ℕ) : IsClosed (targetLevelSet C n k) := by
  exact (hC k).preimage
    ((continuous_fst.comp continuous_subtype_val).prodMk
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)))

omit [TopologicalSpace Y] in
theorem targetLevelSet_cover (F : Y → Y → Prop) (hF : Equivalence F)
    (C : ℕ → Set (Y × Y)) (hcover : ⋃ k, C k = {p | F p.1 p.2}) (n : ℕ) :
    ⋃ k, targetLevelSet C n k = Set.univ := by
  apply eq_univ_of_forall
  intro t
  have hCF : ∀ k, C k ⊆ {p | F p.1 p.2} := by
    intro k p hp
    rw [← hcover]
    exact mem_iUnion.mpr ⟨k, hp⟩
  have hab : F t.val.1 t.val.2.1 := hCF n t.property.1
  have hbc : F t.val.2.1 t.val.2.2 := hCF n t.property.2
  have hac : (t.val.1, t.val.2.2) ∈ ⋃ k, C k := by
    rw [hcover]
    exact hF.trans hab hbc
  obtain ⟨k, hk⟩ := mem_iUnion.mp hac
  exact mem_iUnion.mpr ⟨k, hk⟩

/-- The countable rank bound for one fixed composability level. -/
theorem targetIter_exists_countable_empty [PolishSpace Y]
    (F : Y → Y → Prop) (hF : Equivalence F)
    (C : ℕ → Set (Y × Y)) (hC : ∀ n, IsClosed (C n))
    (hcover : ⋃ k, C k = {p | F p.1 p.2}) (n : ℕ) :
    ∃ ξ : Ordinal.{u}, ξ < ω₁ ∧ targetIter C n ξ = ∅ := by
  letI : PolishSpace (targetTripleSet C n) := (isClosed_targetTripleSet C hC n).polishSpace
  exact coverDerivative_exists_countable_empty (targetLevelSet C n)
    (isClosed_targetLevelSet C hC n) (targetLevelSet_cover F hF C hcover n) isClosed_univ

/-- Lemma 3.1 of the paper: one countable ordinal empties every level of the
composition derivative associated with a fixed closed cover. -/
theorem targetIter_exists_uniform_countable_empty [PolishSpace Y]
    (F : Y → Y → Prop) (hF : Equivalence F)
    (C : ℕ → Set (Y × Y)) (hC : ∀ n, IsClosed (C n))
    (hcover : ⋃ k, C k = {p | F p.1 p.2}) :
    ∃ γ : Ordinal.{u}, γ < ω₁ ∧ ∀ n, targetIter C n γ = ∅ := by
  choose ξ hξ hempty using targetIter_exists_countable_empty F hF C hC hcover
  refine ⟨⨆ n, ξ n, Ordinal.iSup_lt_omega_one hξ, ?_⟩
  intro n
  apply subset_empty_iff.mp
  rw [← hempty n]
  exact derivativeIter_antitone (targetDerivative C n) Set.univ (Ordinal.le_iSup ξ n)

end
end NoUniversalFSigma



namespace NoUniversalFSigma
noncomputable section
universe u
open Set TopologicalSpace
variable {X Y : Type u}

/-- A comparison of removal operations transfers to every ordinal stage. -/
theorem derivativeIter_image_subset
    (D : Set X →o Set X) (E : Set Y →o Set Y) (f : X → Y)
    (hstep : ∀ A B, f '' A ⊆ B → f '' D A ⊆ E B)
    {A : Set X} {B : Set Y} (hAB : f '' A ⊆ B) (ξ : Ordinal.{u}) :
    f '' derivativeIter D A ξ ⊆ derivativeIter E B ξ := by
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
    rintro y ⟨x, hx, rfl⟩
    change x ∈ OrdinalApprox.gfpApprox D A ξ at hx
    change f x ∈ OrdinalApprox.gfpApprox E B ξ
    rw [OrdinalApprox.gfpApprox] at hx ⊢
    refine ⟨hAB ⟨x, hx.1, rfl⟩, ?_⟩
    apply mem_iInter.mpr
    intro η
    apply mem_iInter.mpr
    intro hη
    exact hstep _ _ (IH η hη) ⟨x, mem_iInter.mp (mem_iInter.mp hx.2 η) hη, rfl⟩

variable [TopologicalSpace X]

/-- The cover derivative is precisely unboundedness on every relative neighborhood. -/
theorem mem_coverDerivative_iff (C : ℕ → Set X) (A : Set X) (x : X) :
    x ∈ coverDerivative C A ↔ x ∈ A ∧
      ∀ k U, IsOpen U → x ∈ U → ∃ y ∈ U, y ∈ A ∧ y ∉ C k := by
  constructor
  · rintro ⟨hx, hcl⟩
    refine ⟨hx, ?_⟩
    intro k U hU hxU
    obtain ⟨y, hyU, hyA, hyC⟩ :=
      mem_closure_iff.mp (mem_iInter.mp hcl k) U hU hxU
    exact ⟨y, hyU, hyA, hyC⟩
  · rintro ⟨hx, hlocal⟩
    refine ⟨hx, mem_iInter.mpr fun k => mem_closure_iff.mpr ?_⟩
    intro U hU hxU
    obtain ⟨y, hyU, hyA, hyC⟩ := hlocal k U hU hxU
    exact ⟨y, hyU, hyA, hyC⟩

end
end NoUniversalFSigma

namespace NoUniversalFSigma
noncomputable section
universe u
open Set Ordinal

/-- Every countable ordinal in an arbitrary universe comes from a countable
ordinal in the smallest universe. -/
theorem exists_countable_lift {ξ : Ordinal.{u}} (hξ : ξ < ω₁) :
    ∃ α : Ordinal.{0}, α < ω₁ ∧ Ordinal.lift.{u} α = ξ := by
  have hle : ξ ≤ Ordinal.lift.{u} (ω₁ : Ordinal.{0}) := by simpa using hξ.le
  obtain ⟨α, hα⟩ := Ordinal.mem_range_lift_of_le hle
  refine ⟨α, ?_, hα⟩
  exact Ordinal.lift_lt_omega_one.mp (hα ▸ hξ)

variable {Y : Type u} [TopologicalSpace Y]

/-- The uniform target rank can always be indexed by a small countable ordinal. -/
theorem targetIter_exists_uniform_countable_empty_lift [PolishSpace Y]
    (F : Y → Y → Prop) (hF : Equivalence F)
    (C : ℕ → Set (Y × Y)) (hC : ∀ n, IsClosed (C n))
    (hcover : ⋃ k, C k = {p | F p.1 p.2}) :
    ∃ α : Ordinal.{0}, α < ω₁ ∧ ∀ n, targetIter C n (Ordinal.lift.{u} α) = ∅ := by
  obtain ⟨ξ, hξ, hempty⟩ := targetIter_exists_uniform_countable_empty F hF C hC hcover
  obtain ⟨α, hα, heq⟩ := exists_countable_lift hξ
  exact ⟨α, hα, heq ▸ hempty⟩

end
end NoUniversalFSigma

namespace NoUniversalFSigma
noncomputable section
universe u
open Set
variable {X : Type} {Y : Type u}

/-- Naturality with a small source and an arbitrary-universe target. -/
theorem derivativeIter_image_subset_lift
    (D : Set X →o Set X) (E : Set Y →o Set Y) (f : X → Y)
    (hstep : ∀ A B, f '' A ⊆ B → f '' D A ⊆ E B)
    {A : Set X} {B : Set Y} (hAB : f '' A ⊆ B) (ξ : Ordinal.{0}) :
    f '' derivativeIter D A ξ ⊆ derivativeIter E B (Ordinal.lift.{u} ξ) := by
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
    rintro y ⟨x, hx, rfl⟩
    change x ∈ OrdinalApprox.gfpApprox D A ξ at hx
    change f x ∈ OrdinalApprox.gfpApprox E B (Ordinal.lift.{u} ξ)
    rw [OrdinalApprox.gfpApprox] at hx ⊢
    refine ⟨hAB ⟨x, hx.1, rfl⟩, ?_⟩
    apply mem_iInter.mpr
    intro η
    apply mem_iInter.mpr
    intro hη
    obtain ⟨δ, rfl⟩ := Ordinal.mem_range_lift_of_le hη.le
    have hδ : δ < ξ := Ordinal.lift_lt.mp hη
    exact hstep _ _ (IH δ hδ) ⟨x, mem_iInter.mp (mem_iInter.mp hx.2 δ) hδ, rfl⟩

end
end NoUniversalFSigma

namespace NoUniversalFSigma
noncomputable section
universe u
open Set Ordinal
variable {Y : Type u} [TopologicalSpace Y]

@[simp] theorem targetIter_zero (C : ℕ → Set (Y × Y)) (n : ℕ) :
    targetIter C n 0 = Set.univ := derivativeIter_zero _ _

@[simp] theorem targetIter_succ (C : ℕ → Set (Y × Y)) (n : ℕ) (ξ : Ordinal.{u}) :
    targetIter C n (ξ + 1) = targetDerivative C n (targetIter C n ξ) :=
  derivativeIter_succ _ _ (coverDerivative_subset _) ξ

theorem targetIter_antitone (C : ℕ → Set (Y × Y)) (n : ℕ) :
    Antitone (targetIter C n) := derivativeIter_antitone _ _

theorem targetIter_limit (C : ℕ → Set (Y × Y)) (n : ℕ)
    {ξ : Ordinal.{u}} (hξ : Order.IsSuccLimit ξ) :
    targetIter C n ξ = ⋂ η : Set.Iio ξ, targetIter C n η :=
  derivativeIter_limit _ _ hξ

theorem isClosed_targetIter (C : ℕ → Set (Y × Y)) (n : ℕ) (ξ : Ordinal.{u}) :
    IsClosed (targetIter C n ξ) :=
  isClosed_derivativeIter _ (fun _ => isClosed_coverDerivative _) isClosed_univ ξ

end
end NoUniversalFSigma

end

/- Source module: NoUniversalFSigma.Escape -/
section
set_option autoImplicit false

namespace NoUniversalFSigma

universe u v

variable {P : Type u} {B : Type v}
variable [TopologicalSpace P] [TopologicalSpace B] [Add B]

/-- Sum of two vectors from a parameter family, in the ambient space. -/
def pairSum (j : P → B) (p : P × P) : B := j p.1 + j p.2

/-- Points at which the closures of nearby family sums escape the specified set.
All closures are in the ambient space B, never in its subspace H. -/
def escapeDerivative (H : Set B) (j : P → B) (R : Set (P × P)) : Set (P × P) :=
  {p | p ∈ R ∧ ∀ U : Set (P × P), IsOpen U → p ∈ U →
    ¬ closure (pairSum j '' (R ∩ U)) ⊆ H}

theorem escapeDerivative_subset (H : Set B) (j : P → B) (R : Set (P × P)) :
    escapeDerivative H j R ⊆ R := fun _ hp => hp.1

theorem escapeDerivative_mono (H : Set B) (j : P → B) :
    Monotone (escapeDerivative H j) := by
  intro R S hRS p hp
  refine ⟨hRS hp.1, ?_⟩
  intro U hU hpU hbad
  apply hp.2 U hU hpU
  exact (closure_mono (Set.image_mono (Set.inter_subset_inter_left U hRS))).trans hbad

theorem isClosed_escapeDerivative (H : Set B) (j : P → B)
    {R : Set (P × P)} (hR : IsClosed R) : IsClosed (escapeDerivative H j R) := by
  classical
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  by_cases hpR : p ∈ R
  · have hbad : ¬ ∀ U : Set (P × P), IsOpen U → p ∈ U →
        ¬ closure (pairSum j '' (R ∩ U)) ⊆ H := by
      intro h
      exact hp ⟨hpR, h⟩
    push_neg at hbad
    obtain ⟨U, hU, hpU, hsub⟩ := hbad
    refine ⟨U, ?_, hU, hpU⟩
    intro q hq hqd
    exact hqd.2 U hU hq hsub
  · exact ⟨Rᶜ, fun q hq hqd => hq hqd.1, hR.isOpen_compl, hpR⟩

def escapeOperator (H : Set B) (j : P → B) : Set (P × P) →o Set (P × P) where
  toFun := escapeDerivative H j
  monotone' := escapeDerivative_mono H j

/-- Transfinite escape remainders, starting from all parameter pairs. -/
noncomputable def escapeRemainder (H : Set B) (j : P → B) (ξ : Ordinal) : Set (P × P) :=
  derivativeIter (escapeOperator H j) Set.univ ξ

@[simp] theorem escapeRemainder_zero (H : Set B) (j : P → B) :
    escapeRemainder H j 0 = Set.univ := derivativeIter_zero _ _

@[simp] theorem escapeRemainder_succ (H : Set B) (j : P → B) (ξ : Ordinal) :
    escapeRemainder H j (ξ + 1) = escapeDerivative H j (escapeRemainder H j ξ) :=
  derivativeIter_succ _ _ (escapeDerivative_subset H j) ξ

theorem escapeRemainder_antitone (H : Set B) (j : P → B) :
    Antitone (escapeRemainder H j) := derivativeIter_antitone _ _

theorem isClosed_escapeRemainder (H : Set B) (j : P → B) (ξ : Ordinal) :
    IsClosed (escapeRemainder H j ξ) :=
  isClosed_derivativeIter _ (fun _ => isClosed_escapeDerivative H j) isClosed_univ ξ

section Transfer

variable {Q : Type u} {C : Type*} [TopologicalSpace Q] [TopologicalSpace C] [Add C]

/-- One-step transfer only needs a continuous map of ambient limits that
preserves escaping points and intertwines sums. -/
theorem escapeDerivative_transfer (H : Set B) (K : Set C) (j : P → B) (i : Q → C)
    (a b : Q → P) (ha : Continuous a) (hb : Continuous b)
    (g : C → B) (hg : Continuous g)
    (hsum : ∀ t u, pairSum j (a t, b u) = g (pairSum i (t, u)))
    (hout : ∀ z, z ∉ K → g z ∉ H)
    {R : Set (Q × Q)} {S : Set (P × P)}
    (hRS : Prod.map a b '' R ⊆ S) :
    Prod.map a b '' escapeDerivative K i R ⊆ escapeDerivative H j S := by
  classical
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨hRS ⟨q, hq.1, rfl⟩, ?_⟩
  intro U hU hqU hbad
  have hab : Continuous (Prod.map a b) := ha.prodMap hb
  have hfail := hq.2 ((Prod.map a b) ⁻¹' U) (hU.preimage hab) hqU
  apply hfail
  intro z hz
  by_contra hzK
  apply hout z hzK
  apply hbad
  have hz' : g z ∈ closure (g '' (pairSum i ''
      (R ∩ (Prod.map a b) ⁻¹' U))) :=
    image_closure_subset_closure_image hg ⟨z, hz, rfl⟩
  apply closure_mono (s := g '' (pairSum i '' (R ∩ (Prod.map a b) ⁻¹' U))) ?_ hz'
  rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
  exact ⟨Prod.map a b r, ⟨hRS ⟨r, hr.1, rfl⟩, hr.2⟩, hsum r.1 r.2⟩

theorem escapeRemainder_transfer (H : Set B) (K : Set C) (j : P → B) (i : Q → C)
    (a b : Q → P) (ha : Continuous a) (hb : Continuous b)
    (g : C → B) (hg : Continuous g)
    (hsum : ∀ t u, pairSum j (a t, b u) = g (pairSum i (t, u)))
    (hout : ∀ z, z ∉ K → g z ∉ H) (ξ : Ordinal) :
    Prod.map a b '' escapeRemainder K i ξ ⊆ escapeRemainder H j ξ :=
  derivativeIter_image_subset _ _ (Prod.map a b)
    (fun _ _ h => escapeDerivative_transfer H K j i a b ha hb g hg hsum hout h)
    (Set.subset_univ _) ξ

end Transfer

end NoUniversalFSigma

end

/- Source module: NoUniversalFSigma.HilbertEmbedding -/
section
/-!
# Embedding separable real Hilbert spaces in the fixed `RealL2`

A countable Hilbert basis is sent to distinct standard coordinate vectors.
Completeness makes the resulting isometric range closed.
-/

noncomputable section

open Set TopologicalSpace Topology
open scoped InnerProduct ENNReal

namespace NoUniversalFSigma

universe u v w

/-- Every separable complete real Hilbert space admits a linear isometric
embedding into the standard real `ℓ²` space. Finite-dimensional and zero spaces
are included. -/
theorem exists_linearIsometry_realL2 (B : Type u)
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] [SeparableSpace B] : Nonempty (B →ₗᵢ[ℝ] RealL2) := by
  classical
  obtain ⟨I, b, hb⟩ := exists_hilbertBasis ℝ B
  letI : DiscreteTopology I := discreteTopology_iff_isOpen_singleton.mpr fun j => by
    have hcont : Continuous (fun i : I => inner ℝ (b j) (b i)) := by
      simpa only [hb] using
        (continuous_const.inner (continuous_subtype_val : Continuous (fun i : I => (i : B))))
    have hsingle : {i : I | (1 / 2 : ℝ) < inner ℝ (b j) (b i)} = {j} := by
      ext i
      rw [mem_setOf, mem_singleton_iff, orthonormal_iff_ite.mp b.orthonormal]
      by_cases h : j = i <;> simp [h, eq_comm] <;> norm_num
    rw [← hsingle]
    exact isOpen_lt continuous_const hcont
  letI : Countable I := separableSpace_iff_countable.mp inferInstance
  letI : Encodable I := Encodable.ofCountable I
  let v : I → RealL2 := fun i => lp.single 2 (Encodable.encode i) (1 : ℝ)
  have hv : Orthonormal ℝ v := by
    constructor
    · intro i
      simp [v, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]
    · intro i j hij
      have hcode : Encodable.encode i ≠ Encodable.encode j := Encodable.encode_injective.ne hij
      simp [v, lp.inner_single_left, lp.single_apply, hcode]
  exact ⟨hv.orthogonalFamily.linearIsometry.comp b.repr.toLinearIsometry⟩

/-- A chosen standard-coordinate embedding. -/
def hilbertEmbedding (B : Type u)
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] [SeparableSpace B] : B →ₗᵢ[ℝ] RealL2 :=
  Classical.choice (exists_linearIsometry_realL2 B)

theorem isClosedEmbedding_hilbertEmbedding (B : Type u)
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] [SeparableSpace B] :
    IsClosedEmbedding (hilbertEmbedding B) :=
  ⟨(hilbertEmbedding B).isometry.isEmbedding,
    (hilbertEmbedding B).isometry.isUniformInducing.isComplete_range.isClosed⟩

section Transport

variable {B : Type u} {D : Type v}
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D]

/-- An isometric image of an `Fσ` set is `Fσ` when the source Hilbert
space is complete. -/
theorem isFSigma_image_linearIsometry [CompleteSpace B]
    (e : B →ₗᵢ[ℝ] D) {S : Set B} (hS : IsFSigma S) : IsFSigma (e '' S) := by
  obtain ⟨K, hK, rfl⟩ := hS
  exact ⟨fun n => e '' K n,
    fun n => e.isometry.isClosedEmbedding.isClosedMap _ (hK n), image_iUnion⟩

/-- The algebraic image of an `Fσ` submodule is `Fσ`. -/
theorem isFSigma_map_submodule [CompleteSpace B]
    (e : B →ₗᵢ[ℝ] D) (H : Submodule ℝ B) (hH : IsFSigma (H : Set B)) :
    IsFSigma (H.map e.toLinearMap : Set D) :=
  isFSigma_image_linearIsometry e hH

/-- Taking the algebraic span commutes with the coordinate embedding. -/
theorem span_range_comp_linearIsometry {P : Type w}
    (e : B →ₗᵢ[ℝ] D) (j : P → B) :
    Submodule.span ℝ (range (fun t => e (j t))) =
      (Submodule.span ℝ (range j)).map e.toLinearMap := by
  rw [Submodule.map_span, ← range_comp]
  rfl

/-- A closed branch embedding stays closed after an ambient isometric embedding. -/
theorem isClosedEmbedding_comp_linearIsometry [CompleteSpace B]
    {P : Type w} [TopologicalSpace P] (e : B →ₗᵢ[ℝ] D)
    {j : P → B} (hj : IsClosedEmbedding j) : IsClosedEmbedding (fun t => e (j t)) :=
  e.isometry.isClosedEmbedding.comp hj

/-- Escaping ambient limits remain escaping after an injective isometric
embedding. This transports ranks without restricting a Baire-measurable map
to a possibly nowhere-dense closed subspace. -/
theorem escapeRemainder_image_linearIsometry
    {P : Type w} [TopologicalSpace P] (e : B →ₗᵢ[ℝ] D)
    (H : Set B) (j : P → B) (ξ : Ordinal.{w}) :
    escapeRemainder H j ξ ⊆ escapeRemainder (e '' H) (fun t => e (j t)) ξ := by
  have h := escapeRemainder_transfer (e '' H) H (fun t => e (j t)) j
    id id continuous_id continuous_id e e.continuous
    (fun t r => (e.map_add (j t) (j r)).symm)
    (fun z hz => by
      rintro ⟨a, ha, he⟩
      exact hz (e.injective he ▸ ha)) ξ
  simpa only [Prod.map_id, image_id] using h

/-- The adjoint of an isometric embedding is a left inverse. -/
theorem adjoint_linearIsometry_apply [CompleteSpace B] [CompleteSpace D]
    (e : B →ₗᵢ[ℝ] D) (x : B) :
    ContinuousLinearMap.adjoint e.toContinuousLinearMap (e x) = x := by
  have h := (ContinuousLinearMap.isometry_iff_adjoint_comp_self e.toContinuousLinearMap).mp e.isometry
  have hx := congrArg (fun T : B →L[ℝ] B => T x) h
  exact hx

/-- A bounded functional on a source Hilbert space extends to the ambient
Hilbert space by composing with the adjoint of the embedding. -/
def extendFunctional [CompleteSpace B] [CompleteSpace D]
    (e : B →ₗᵢ[ℝ] D) (ℓ : B →L[ℝ] ℝ) : D →L[ℝ] ℝ :=
  ℓ.comp (ContinuousLinearMap.adjoint e.toContinuousLinearMap)

@[simp] theorem extendFunctional_apply_embedding [CompleteSpace B] [CompleteSpace D]
    (e : B →ₗᵢ[ℝ] D) (ℓ : B →L[ℝ] ℝ) (x : B) :
    extendFunctional e ℓ (e x) = ℓ x := by
  simp only [extendFunctional, ContinuousLinearMap.comp_apply, adjoint_linearIsometry_apply]

/-- Under Riesz representation, extending a functional simply embeds its
representing vector. In particular no increase in its norm is necessary. -/
theorem extendFunctional_eq_toDual [CompleteSpace B] [CompleteSpace D]
    (e : B →ₗᵢ[ℝ] D) (ℓ : B →L[ℝ] ℝ) :
    extendFunctional e ℓ =
      InnerProductSpace.toDual ℝ D (e ((InnerProductSpace.toDual ℝ B).symm ℓ)) := by
  ext y
  change ℓ (ContinuousLinearMap.adjoint e.toContinuousLinearMap y) =
    inner ℝ (e ((InnerProductSpace.toDual ℝ B).symm ℓ)) y
  rw [← InnerProductSpace.toDual_symm_apply]
  exact ContinuousLinearMap.adjoint_inner_right e.toContinuousLinearMap _ y

@[simp] theorem norm_extendFunctional [CompleteSpace B] [CompleteSpace D]
    (e : B →ₗᵢ[ℝ] D) (ℓ : B →L[ℝ] ℝ) : ‖extendFunctional e ℓ‖ = ‖ℓ‖ := by
  rw [extendFunctional_eq_toDual, LinearIsometryEquiv.norm_map,
    e.norm_map, LinearIsometryEquiv.norm_map]

end Transport

end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.BranchFamily -/
section
/-!
# The concrete Hilbert branch family

This file develops the actual square-summable branch vectors used in section 5.
The span here is the algebraic real span, with no topological closure.
-/

noncomputable section

open scoped BigOperators ENNReal
open Set Filter Topology

namespace NoUniversalFSigma
namespace Branch

abbrev Parameter := ℕ → ℕ
abbrev Node := List ℕ
abbrev Coordinate := Node ⊕ (Node × ℕ)
abbrev Hilbert := lp (fun _ : Coordinate => ℝ) 2

/-- The branchPrefix of length `n` of a branch. -/
def branchPrefix (x : Parameter) (n : ℕ) : Node :=
  List.ofFn (fun i : Fin n => x i)

@[simp] theorem length_prefix (x : Parameter) (n : ℕ) :
    (branchPrefix x n).length = n := by simp [branchPrefix]

/-- Weights decrease with both depth and the labels on the preceding edges. -/
def weight (s : Node) : ℝ := (1 / 2 : ℝ) ^ (s.sum + 2 * s.length)

theorem weight_pos (s : Node) : 0 < weight s := by
  exact pow_pos (by norm_num) _

theorem weight_le_depth (s : Node) : weight s ≤ (1 / 4 : ℝ) ^ s.length := by
  calc
    weight s ≤ (1 / 2 : ℝ) ^ (2 * s.length) := by
      apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
      omega
    _ = (1 / 4 : ℝ) ^ s.length := by rw [pow_mul]; norm_num

@[simp] theorem weight_nil : weight [] = 1 := by simp [weight]

theorem weight_append (s : Node) (k : ℕ) :
    weight (s ++ [k]) = weight s * (1 / 2 : ℝ) ^ (k + 2) := by
  simp only [weight, List.sum_append, List.sum_cons, List.sum_nil,
    List.length_append, List.length_singleton]
  rw [← pow_add]
  congr 1
  omega

/-- The two signed basis coordinates attached to level `n` of `x`. -/
def term (x : Parameter) (n : ℕ) : Hilbert :=
  weight (branchPrefix x n) •
    (lp.single 2 (Sum.inl (branchPrefix x n)) (1 : ℝ) +
      lp.single 2 (Sum.inr (branchPrefix x n, x n / 2)) ((-1 : ℝ) ^ x n))

theorem norm_term_le (x : Parameter) (n : ℕ) :
    ‖term x n‖ ≤ 2 * (1 / 4 : ℝ) ^ n := by
  have hs : ‖(lp.single 2 (Sum.inl (branchPrefix x n)) (1 : ℝ) : Hilbert) +
      lp.single 2 (Sum.inr (branchPrefix x n, x n / 2)) ((-1 : ℝ) ^ x n)‖ ≤ 2 := by
    calc
      _ ≤ ‖(lp.single 2 (Sum.inl (branchPrefix x n)) (1 : ℝ) : Hilbert)‖ +
          ‖(lp.single 2 (Sum.inr (branchPrefix x n, x n / 2)) ((-1 : ℝ) ^ x n) : Hilbert)‖ :=
        norm_add_le _ _
      _ = 2 := by rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num)]
                  norm_num
  rw [term, norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos _)]
  calc
    _ ≤ weight (branchPrefix x n) * 2 := mul_le_mul_of_nonneg_left hs (weight_pos _).le
    _ ≤ (1 / 4 : ℝ) ^ n * 2 := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      simpa using weight_le_depth (branchPrefix x n)
    _ = _ := by ring

theorem summable_bound : Summable (fun n : ℕ => 2 * (1 / 4 : ℝ) ^ n) := by
  exact (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left 2

theorem summable_term (x : Parameter) : Summable (term x) := by
  exact Summable.of_norm_bounded summable_bound (norm_term_le x)

/-- The branch family in the real Hilbert space on the countable coordinate set. -/
def family (x : Parameter) : Hilbert := ∑' n, term x n

theorem term_depends_on_prefix (x y : Parameter) (n : ℕ)
    (h : ∀ i ≤ n, x i = y i) : term x n = term y n := by
  have hp : branchPrefix x n = branchPrefix y n := by
    apply congrArg List.ofFn
    funext i
    exact h i (Nat.le_of_lt i.isLt)
  simp [term, hp, h n le_rfl]

theorem continuous_term (n : ℕ) : Continuous (fun x : Parameter => term x n) := by
  let restriction : Parameter → (Fin (n + 1) → ℕ) := fun x i => x i
  have hr : Continuous restriction := continuous_pi fun i => continuous_apply (i : ℕ)
  let extension : (Fin (n + 1) → ℕ) → Parameter :=
    fun a k => if h : k < n + 1 then a ⟨k, h⟩ else 0
  have he : Continuous (fun a : Fin (n + 1) → ℕ => term (extension a) n) :=
    continuous_of_discreteTopology
  have hfun : (fun x : Parameter => term x n) =
      (fun x => term (extension (restriction x)) n) := by
    funext x
    apply term_depends_on_prefix
    intro i hi
    simp only [extension, restriction]
    rw [dif_pos (by omega)]
  rw [hfun]
  exact he.comp hr

theorem continuous_family : Continuous family := by
  exact continuous_tsum continuous_term summable_bound (fun n x => norm_term_le x n)

theorem term_apply (x : Parameter) (n : ℕ) (c : Coordinate) :
    term x n c = weight (branchPrefix x n) *
      ((Pi.single (Sum.inl (branchPrefix x n)) (1 : ℝ) : Coordinate → ℝ) c +
        (Pi.single (Sum.inr (branchPrefix x n, x n / 2)) ((-1 : ℝ) ^ x n) : Coordinate → ℝ) c) := rfl

theorem term_h_coordinate (x : Parameter) (n : ℕ) (s : Node) :
    term x n (Sum.inl s) = if branchPrefix x n = s then weight s else 0 := by
  rw [term_apply]
  by_cases h : branchPrefix x n = s
  · simp [h, Pi.single_apply]
  · have hn : s ≠ branchPrefix x n := Ne.symm h
    simp [h, hn, Pi.single_apply]

theorem term_e_coordinate (x : Parameter) (n : ℕ) (s : Node) (k : ℕ) :
    term x n (Sum.inr (s, k)) =
      if branchPrefix x n = s ∧ x n / 2 = k then weight s * (-1 : ℝ) ^ x n else 0 := by
  rw [term_apply]
  by_cases h : branchPrefix x n = s ∧ x n / 2 = k
  · rcases h with ⟨h₁, h₂⟩
    simp [h₁, h₂, Pi.single_apply]
  · have hn : (s, k) ≠ (branchPrefix x n, x n / 2) := by
      intro he
      apply h
      exact ⟨(congrArg Prod.fst he).symm, (congrArg Prod.snd he).symm⟩
    simp [h, hn, Pi.single_apply]

theorem family_h_coordinate (x : Parameter) (s : Node) :
    family x (Sum.inl s) = if branchPrefix x s.length = s then weight s else 0 := by
  change (lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 (Sum.inl s)) (∑' n, term x n) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_term x)]
  simp only [lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply]
  rw [tsum_eq_single s.length]
  · exact term_h_coordinate x s.length s
  · intro n hn
    have hp : branchPrefix x n ≠ s := by
      intro he
      have := congrArg List.length he
      simp only [length_prefix] at this
      exact hn this
    simp [term_h_coordinate, hp]

theorem family_e_coordinate (x : Parameter) (s : Node) (k : ℕ) :
    family x (Sum.inr (s, k)) =
      if branchPrefix x s.length = s ∧ x s.length / 2 = k then
        weight s * (-1 : ℝ) ^ x s.length else 0 := by
  change (lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 (Sum.inr (s, k)))
    (∑' n, term x n) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_term x)]
  simp only [lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply]
  rw [tsum_eq_single s.length]
  · exact term_e_coordinate x s.length s k
  · intro n hn
    have hp : branchPrefix x n ≠ s := by
      intro he
      have := congrArg List.length he
      simp only [length_prefix] at this
      exact hn this
    simp [term_e_coordinate, hp]

/-- The root coordinate is a continuous mass functional equal to one on each atom. -/
def mass : Hilbert →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 (Sum.inl [])

@[simp] theorem mass_family (x : Parameter) : mass (family x) = 1 := by
  change family x (Sum.inl []) = 1
  simp [family_h_coordinate, branchPrefix]

theorem family_injective : Function.Injective family := by
  intro x y h
  have hp (n : ℕ) : branchPrefix x n = branchPrefix y n := by
    have he := congrArg (fun v : Hilbert => v (Sum.inl (branchPrefix x n))) h
    change family x (Sum.inl (branchPrefix x n)) = family y (Sum.inl (branchPrefix x n)) at he
    rw [family_h_coordinate, family_h_coordinate] at he
    simp only [length_prefix, if_pos rfl] at he
    by_contra hn
    rw [if_neg (Ne.symm hn)] at he
    exact (weight_pos _).ne' he
  funext n
  have he := List.ofFn_injective (hp (n + 1))
  exact congrFun he ⟨n, Nat.lt_succ_self n⟩

theorem norm_family_le (x : Parameter) : ‖family x‖ ≤ 8 / 3 := by
  have h := tsum_of_norm_bounded
    ((hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left 2)
    (norm_term_le x)
  norm_num [family] at h ⊢
  exact h

theorem branchPrefix_succ (x : Parameter) (n : ℕ) :
    branchPrefix x (n + 1) = branchPrefix x n ++ [x n] := by
  simpa [branchPrefix, List.concat_eq_append] using
    (List.ofFn_succ' (fun i : Fin (n + 1) => x i))

/-- Distinct next digits have a fixed positive Hilbert separation, independent
of the size of either digit. The signed sibling coordinate is essential here. -/
theorem digit_gap (x y : Parameter) (n : ℕ) (s : Node)
    (hx : branchPrefix x n = s) (hy : branchPrefix y n = s)
    (hne : x n ≠ y n) : weight s ≤ ‖family x - family y‖ := by
  have hl : s.length = n := by simpa using (congrArg List.length hx).symm
  have hnorm := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (family x - family y) (Sum.inr (s, x n / 2))
  change ‖family x (Sum.inr (s, x n / 2)) - family y (Sum.inr (s, x n / 2))‖ ≤ _ at hnorm
  rw [family_e_coordinate, family_e_coordinate] at hnorm
  simp only [hl, hx, hy, true_and, and_self, if_pos] at hnorm
  by_cases hdiv : y n / 2 = x n / 2
  · rw [if_pos hdiv] at hnorm
    have hmod : x n % 2 ≠ y n % 2 := by omega
    have hm₁ : x n % 2 < 2 := Nat.mod_lt _ (by omega)
    have hm₂ : y n % 2 < 2 := Nat.mod_lt _ (by omega)
    rw [neg_one_pow_eq_pow_mod_two (R := ℝ) (x n),
      neg_one_pow_eq_pow_mod_two (R := ℝ) (y n)] at hnorm
    interval_cases h₁ : x n % 2 <;> interval_cases h₂ : y n % 2 <;>
      simp_all [Real.norm_eq_abs] <;>
      linarith [weight_pos s, le_abs_self (weight s + weight s),
        neg_le_abs (-weight s - weight s)]
  · rw [if_neg hdiv, sub_zero, norm_mul, norm_pow] at hnorm
    simpa [Real.norm_eq_abs, abs_of_pos (weight_pos s)] using hnorm

/-- Hilbert Cauchy sequences of branch vectors eventually stabilize each finite prefix. -/
theorem cauchy_prefix_stabilizes (u : ℕ → Parameter)
    (hu : CauchySeq (fun m => family (u m))) (n : ℕ) :
    ∃ s : Node, s.length = n ∧ ∀ᶠ m in atTop, branchPrefix (u m) n = s := by
  induction n with
  | zero => exact ⟨[], rfl, Eventually.of_forall (fun _ => by simp [branchPrefix])⟩
  | succ n ih =>
    obtain ⟨s, hs, hstable⟩ := ih
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 hstable
    obtain ⟨N₂, hN₂⟩ := Metric.cauchySeq_iff.1 hu (weight s) (weight_pos s)
    let N := max N₁ N₂
    refine ⟨s ++ [u N n], by simp [hs], ?_⟩
    filter_upwards [eventually_ge_atTop N] with m hm
    have hm₁ : N₁ ≤ m := le_trans (le_max_left _ _) hm
    have hm₂ : N₂ ≤ m := le_trans (le_max_right _ _) hm
    have hN₁' : N₁ ≤ N := le_max_left _ _
    have hN₂' : N₂ ≤ N := le_max_right _ _
    have hdigit : u m n = u N n := by
      by_contra hne
      have hgap := digit_gap (u m) (u N) n s (hN₁ m hm₁) (hN₁ N hN₁') hne
      have hdist := hN₂ m hm₂ N hN₂'
      rw [dist_eq_norm] at hdist
      exact (not_lt_of_ge hgap) hdist
    rw [branchPrefix_succ, hN₁ m hm₁, hdigit]

theorem cauchy_parameter_limit (u : ℕ → Parameter)
    (hu : CauchySeq (fun m => family (u m))) :
    ∃ x : Parameter, Tendsto u atTop (𝓝 x) := by
  have hdigit (n : ℕ) : ∃ a : ℕ, ∀ᶠ m in atTop, u m n = a := by
    obtain ⟨s, hs, hstable⟩ := cauchy_prefix_stabilizes u hu (n + 1)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hstable
    refine ⟨u M n, ?_⟩
    filter_upwards [hstable] with m hm
    have he : branchPrefix (u m) (n + 1) = branchPrefix (u M) (n + 1) :=
      hm.trans (hM M le_rfl).symm
    exact congrFun (List.ofFn_injective he) ⟨n, Nat.lt_succ_self n⟩
  choose x hx using hdigit
  refine ⟨x, tendsto_pi_nhds.2 (fun n => ?_)⟩
  exact tendsto_const_nhds.congr' (Filter.Eventually.mono (hx n) (fun _ h => h.symm))

theorem isClosed_range_family : IsClosed (Set.range family) := by
  apply IsSeqClosed.isClosed
  intro v z hv hz
  choose u hu using hv
  have he : v = fun m => family (u m) := funext (fun m => (hu m).symm)
  rw [he] at hz
  obtain ⟨x, hx⟩ := cauchy_parameter_limit u hz.cauchySeq
  have hfamily := continuous_family.continuousAt.tendsto.comp hx
  exact ⟨x, tendsto_nhds_unique hfamily hz⟩

def rangeInverse (v : Set.range family) : Parameter := Classical.choose v.property

@[simp] theorem family_rangeInverse (v : Set.range family) : family (rangeInverse v) = v :=
  Classical.choose_spec v.property

theorem continuous_rangeInverse : Continuous rangeInverse := by
  apply SeqContinuous.continuous
  intro v z hz
  have hfamily : Tendsto (fun m => family (rangeInverse (v m))) atTop
      (𝓝 (family (rangeInverse z))) := by
    simpa only [family_rangeInverse] using (continuous_subtype_val.tendsto z).comp hz
  obtain ⟨x, hx⟩ := cauchy_parameter_limit (fun m => rangeInverse (v m)) hfamily.cauchySeq
  have hxeq : x = rangeInverse z := by
    apply family_injective
    exact tendsto_nhds_unique (continuous_family.continuousAt.tendsto.comp hx) hfamily
  simpa [hxeq] using hx

theorem isClosedEmbedding_family : IsClosedEmbedding family := by
  have hleft : Function.LeftInverse rangeInverse (Set.rangeFactorization family) := by
    intro x
    apply family_injective
    exact family_rangeInverse (Set.rangeFactorization family x)
  have hr : Continuous (Set.rangeFactorization family) :=
    continuous_family.subtype_mk _
  have he := hleft.isEmbedding continuous_rangeInverse hr
  exact ⟨IsEmbedding.subtypeVal.comp he, isClosed_range_family⟩

/-- The algebraic span, not its closure. -/
def span : Submodule ℝ Hilbert := Submodule.span ℝ (Set.range family)

theorem family_mem_span (x : Parameter) : family x ∈ span :=
  Submodule.subset_span (Set.mem_range_self x)

end Branch
end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.ClosedCover -/
section
set_option autoImplicit false

namespace NoUniversalFSigma

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem isFSigma_of_isClosed {s : Set X} (hs : IsClosed s) : IsFSigma s := by
  refine ⟨fun _ => s, fun _ => hs, ?_⟩
  ext x
  exact ⟨fun hx => Set.mem_iUnion.mpr ⟨0, hx⟩,
    fun hx => (Set.mem_iUnion.mp hx).choose_spec⟩

theorem isFSigma_empty : IsFSigma (∅ : Set X) := isFSigma_of_isClosed isClosed_empty

theorem isFSigma_univ : IsFSigma (Set.univ : Set X) := isFSigma_of_isClosed isClosed_univ

theorem IsFSigma.preimage {s : Set Y} (hs : IsFSigma s) {f : X → Y}
    (hf : Continuous f) : IsFSigma (f ⁻¹' s) := by
  obtain ⟨C, hC, rfl⟩ := hs
  exact ⟨fun n => f ⁻¹' C n, fun n => (hC n).preimage hf, by simp⟩

theorem IsFSigma.union {s t : Set X} (hs : IsFSigma s) (ht : IsFSigma t) :
    IsFSigma (s ∪ t) := by
  obtain ⟨C, hC, rfl⟩ := hs
  obtain ⟨D, hD, rfl⟩ := ht
  refine ⟨fun n => C n ∪ D n, fun n => (hC n).union (hD n), ?_⟩
  ext x
  simp only [Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (⟨n, hn⟩ | ⟨n, hn⟩)
    · exact ⟨n, Or.inl hn⟩
    · exact ⟨n, Or.inr hn⟩
  · rintro ⟨n, hn | hn⟩
    · exact Or.inl ⟨n, hn⟩
    · exact Or.inr ⟨n, hn⟩

theorem IsFSigma.inter_isClosed {s t : Set X} (hs : IsFSigma s) (ht : IsClosed t) :
    IsFSigma (s ∩ t) := by
  obtain ⟨C, hC, rfl⟩ := hs
  refine ⟨fun n => C n ∩ t, fun n => (hC n).inter ht, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  exact ⟨fun ⟨⟨n, hn⟩, ht⟩ => ⟨n, hn, ht⟩,
    fun ⟨n, hn, ht⟩ => ⟨⟨n, hn⟩, ht⟩⟩

theorem isFSigma_iUnion {s : ℕ → Set X} (hs : ∀ n, IsFSigma (s n)) :
    IsFSigma (⋃ n, s n) := by
  classical
  choose C hC hEq using hs
  refine ⟨fun n => C (Nat.unpair n).1 (Nat.unpair n).2,
    fun n => hC _ _, ?_⟩
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [hEq i] at hi
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hi
    exact ⟨Nat.pair i j, by simpa using hj⟩
  · rintro ⟨n, hn⟩
    refine ⟨(Nat.unpair n).1, ?_⟩
    rw [hEq]
    exact Set.mem_iUnion.mpr ⟨(Nat.unpair n).2, hn⟩

theorem IsFSigma.inter {s t : Set X} (hs : IsFSigma s) (ht : IsFSigma t) :
    IsFSigma (s ∩ t) := by
  obtain ⟨C, hC, rfl⟩ := ht
  have h : s ∩ ⋃ n, C n = ⋃ n, s ∩ C n := by ext x; simp
  rw [h]
  exact isFSigma_iUnion fun n => hs.inter_isClosed (hC n)

theorem IsFSigma.measurableSet {s : Set X} (hs : IsFSigma s) :
    @MeasurableSet X (borel X) s := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  obtain ⟨C, hC, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hC n).measurableSet

theorem isFSigma_cosetRelation (H : Submodule ℝ RealL2)
    (hH : IsFSigma (H : Set RealL2)) : IsFSigmaRelation (CosetRelation H) := by
  exact hH.preimage (continuous_fst.sub continuous_snd)

theorem isFSigma_relation_swap {E : X → X → Prop} (hE : IsFSigmaRelation E) :
    IsFSigmaRelation (fun x y => E y x) :=
  hE.preimage continuous_swap

/-- A normalized closed exhaustion of a fixed equivalence relation. Individual
levels are reflexive and symmetric, but need not be transitive. -/
structure ClosedRelationCover (F : Setoid X) where
  level : ℕ → Set (X × X)
  isClosed_level : ∀ n, IsClosed (level n)
  monotone_level : Monotone level
  reflexive_level : ∀ n x, (x, x) ∈ level n
  symmetric_level : ∀ n x y, (x, y) ∈ level n → (y, x) ∈ level n
  subset_relation : ∀ n p, p ∈ level n → F.r p.1 p.2
  covers : ∀ x y, F.r x y → ∃ n, (x, y) ∈ level n

theorem ClosedRelationCover.iUnion_eq {F : Setoid X} (C : ClosedRelationCover F) :
    ⋃ n, C.level n = {p | F.r p.1 p.2} := by
  ext p
  exact ⟨fun hp => by obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp; exact C.subset_relation n p hn,
    fun hp => Set.mem_iUnion.mpr (C.covers p.1 p.2 hp)⟩

theorem exists_closedRelationCover [T2Space X] (F : Setoid X)
    (hF : IsFSigmaRelation F.r) : Nonempty (ClosedRelationCover F) := by
  classical
  obtain ⟨C, hC, hEq⟩ := hF
  let D : ℕ → Set (X × X) := fun n => C n ∪ Prod.swap ⁻¹' C n
  let L : ℕ → Set (X × X) := fun n =>
    Set.diagonal X ∪ ⋃ k ∈ Finset.range (n + 1), D k
  have hCF : ∀ n p, p ∈ C n → F.r p.1 p.2 := by
    intro n p hp
    have : p ∈ ⋃ n, C n := Set.mem_iUnion.mpr ⟨n, hp⟩
    rw [← hEq] at this
    exact this
  have hDclosed : ∀ n, IsClosed (D n) := fun n =>
    (hC n).union ((hC n).preimage continuous_swap)
  have hLclosed : ∀ n, IsClosed (L n) := fun n =>
    isClosed_diagonal.union (isClosed_biUnion_finset fun k _ => hDclosed k)
  refine ⟨⟨L, hLclosed, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro n m hnm p hp
    rcases hp with hp | hp
    · exact Or.inl hp
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
      obtain ⟨hk, hp⟩ := Set.mem_iUnion.mp hk
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le (Nat.add_le_add_right hnm 1)), hp⟩⟩)
  · intro n x
    exact Or.inl rfl
  · intro n x y hxy
    rcases hxy with hxy | hxy
    · exact Or.inl hxy.symm
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hxy
      obtain ⟨hk, hxy⟩ := Set.mem_iUnion.mp hk
      exact Or.inr (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨hk, by
        change (y, x) ∈ C k ∪ Prod.swap ⁻¹' C k
        rcases hxy with hxy | hxy
        · exact Or.inr hxy
        · exact Or.inl hxy⟩⟩)
  · intro n p hp
    rcases hp with hp | hp
    · change p.1 = p.2 at hp
      simpa only [← hp] using F.refl p.1
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hp
      obtain ⟨_, hp⟩ := Set.mem_iUnion.mp hk
      rcases hp with hp | hp
      · exact hCF k p hp
      · exact F.symm (hCF k p.swap hp)
  · intro x y hxy
    have hxy' : (x, y) ∈ ⋃ n, C n := by rw [← hEq]; exact hxy
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxy'
    refine ⟨n, Or.inr (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨?_, Or.inl hn⟩⟩)⟩
    exact Finset.mem_range.mpr (Nat.lt_succ_self n)

end NoUniversalFSigma

end

/- Source module: NoUniversalFSigma.BranchSpan -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open Set Filter Topology
namespace NoUniversalFSigma.Branch

def mask (keep : Coordinate → Prop) (v : Hilbert) : Hilbert :=
  ⟨fun c => if keep c then v c else 0,
    (lp.memℓp v).mono' (fun c => by split_ifs <;> simp)⟩

@[simp] theorem mask_apply (keep : Coordinate → Prop) (v : Hilbert) (c : Coordinate) :
    mask keep v c = if keep c then v c else 0 := rfl

def maskLinear (keep : Coordinate → Prop) : Hilbert →ₗ[ℝ] Hilbert where
  toFun := mask keep
  map_add' v w := by
    ext c
    change (if keep c then v c + w c else 0) =
      ((if keep c then v c else 0) + (if keep c then w c else 0))
    split_ifs <;> simp
  map_smul' a v := by
    ext c
    change (if keep c then a * v c else 0) = a * (if keep c then v c else 0)
    split_ifs <;> simp

theorem norm_mask_le (keep : Coordinate → Prop) (v : Hilbert) : ‖mask keep v‖ ≤ ‖v‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro c
  simp only [mask_apply]
  split_ifs <;> simp

def maskCLM (keep : Coordinate → Prop) : Hilbert →L[ℝ] Hilbert :=
  (maskLinear keep).mkContinuous 1 (fun v => by simpa using norm_mask_le keep v)

@[simp] theorem maskCLM_apply (keep : Coordinate → Prop) (v : Hilbert) (c : Coordinate) :
    maskCLM keep v c = if keep c then v c else 0 := rfl

theorem maskCLM_single (keep : Coordinate → Prop) (c : Coordinate) (a : ℝ) :
    maskCLM keep (lp.single 2 c a : Hilbert) =
      if keep c then (lp.single 2 c a : Hilbert) else 0 := by
  by_cases hk : keep c
  · rw [if_pos hk]
    ext d
    rw [maskCLM_apply]
    by_cases h : d = c
    · subst d; simp [hk]
    · simp [lp.single_apply, Pi.single_eq_of_ne h]
  · rw [if_neg hk]
    ext d
    change (if keep d then (lp.single 2 c a : Hilbert) d else 0) = 0
    by_cases h : d = c
    · subst d; simp [hk]
    · simp [lp.single_apply, Pi.single_eq_of_ne h]

def attached : Coordinate → Node := Sum.elim id Prod.fst

def projection (s : Node) : Hilbert →L[ℝ] Hilbert :=
  maskCLM (fun c => s <+: attached c)

theorem branchPrefix_mono (x : Parameter) {m n : ℕ} (h : m ≤ n) :
    branchPrefix x m <+: branchPrefix x n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n hn ih =>
    rw [branchPrefix_succ]
    exact ih.trans (List.prefix_append _ _)

theorem projection_term (s : Node) (x : Parameter) (hx : branchPrefix x s.length = s)
    (n : ℕ) : projection s (term x n) = if s.length ≤ n then term x n else 0 := by
  have hp : (s <+: branchPrefix x n) ↔ s.length ≤ n := by
    constructor
    · intro h; simpa using h.length_le
    · intro h; simpa [hx] using branchPrefix_mono x h
  simp only [term, projection, map_smul, map_add, maskCLM_single, attached,
    Sum.elim_inl, Sum.elim_inr, id_eq, hp]
  split_ifs <;> simp

def cylinder (s : Node) : Set Parameter :=
  {x | ∀ i : Fin s.length, x i = s[i]}

theorem mem_cylinder_iff (s : Node) (x : Parameter) :
    x ∈ cylinder s ↔ branchPrefix x s.length = s := by
  have hs : List.ofFn (fun i : Fin s.length => s[i]) = s := List.ofFn_getElem
  constructor
  · intro hx
    exact (congrArg List.ofFn (funext hx)).trans hs
  · intro hx i
    exact congrFun (List.ofFn_injective (hx.trans hs.symm)) i

theorem isClosed_cylinder (s : Node) : IsClosed (cylinder s) := by
  change IsClosed {x : Parameter | ∀ i : Fin s.length, x i = s[i]}
  simp only [setOf_forall]
  exact isClosed_iInter (fun i => isClosed_eq (continuous_apply (i : ℕ)) continuous_const)

def prefixPart (x : Parameter) (L : ℕ) : Hilbert := ∑ n ∈ Finset.range L, term x n

theorem family_eq_prefixPart_add_projection (s : Node) (x : Parameter)
    (hx : branchPrefix x s.length = s) :
    family x = prefixPart x s.length + projection s (family x) := by
  rw [family, ContinuousLinearMap.map_tsum _ (summable_term x)]
  simp only [projection_term s x hx]
  have he : (∑' n : ℕ, if s.length ≤ n then term x n else 0) =
      ∑' n : {n : ℕ // n ∉ Finset.range s.length}, term x n := by
    calc
      _ = ∑' n : ℕ, ({n : ℕ | n ∉ Finset.range s.length} : Set ℕ).indicator (term x) n := by
        congr 1
        funext n
        simp [Set.indicator, Finset.mem_range, not_lt]
      _ = _ := (tsum_subtype {n : ℕ | n ∉ Finset.range s.length} (term x)).symm
  rw [he]
  exact ((summable_term x).sum_add_tsum_subtype_compl (Finset.range s.length)).symm

theorem prefixPart_eq (x y : Parameter) (L : ℕ)
    (h : branchPrefix x L = branchPrefix y L) : prefixPart x L = prefixPart y L := by
  have hxy := List.ofFn_injective h
  apply Finset.sum_congr rfl
  intro n hn
  apply term_depends_on_prefix
  intro i hi
  exact congrFun hxy ⟨i, by have := Finset.mem_range.1 hn; omega⟩

theorem isClosed_tailImage (s : Node) : IsClosed (projection s '' (family '' cylinder s)) := by
  apply IsSeqClosed.isClosed
  intro v z hv hz
  have hv' (m : ℕ) : ∃ x ∈ cylinder s, projection s (family x) = v m := by
    obtain ⟨w, ⟨x, hx, rfl⟩, hw⟩ := hv m
    exact ⟨x, hx, hw⟩
  choose u hu hprojection using hv'
  have he (m : ℕ) : family (u m) = prefixPart (u 0) s.length + v m := by
    rw [family_eq_prefixPart_add_projection s (u m) ((mem_cylinder_iff s _).1 (hu m))]
    rw [hprojection m]
    rw [prefixPart_eq (u m) (u 0) s.length
      (((mem_cylinder_iff s _).1 (hu m)).trans ((mem_cylinder_iff s _).1 (hu 0)).symm)]
  have hf : Tendsto (fun m => family (u m)) atTop (𝓝 (prefixPart (u 0) s.length + z)) := by
    simpa only [he] using tendsto_const_nhds.add hz
  have hclosed : IsClosed (family '' cylinder s) :=
    isClosedEmbedding_family.isClosedMap _ (isClosed_cylinder s)
  obtain ⟨x, hx, hxeq⟩ := hclosed.mem_of_tendsto hf
    (Eventually.of_forall (fun m => ⟨u m, hu m, rfl⟩))
  have hp : Tendsto (fun m => projection s (family (u m))) atTop (𝓝 (projection s (family x))) := by
    rw [hxeq]
    exact (projection s).continuous.continuousAt.tendsto.comp hf
  have hz' : Tendsto (fun m => projection s (family (u m))) atTop (𝓝 z) := by
    simpa only [hprojection] using hz
  exact ⟨family x, ⟨x, hx, rfl⟩, tendsto_nhds_unique hp hz'⟩

theorem projection_family_other (s t : Node) (x : Parameter)
    (hlen : s.length = t.length) (hne : s ≠ t) (hx : branchPrefix x t.length = t) :
    projection s (family x) = 0 := by
  have hn (n : ℕ) : ¬s <+: branchPrefix x n := by
    intro hs
    have hsn : s.length ≤ n := by simpa using hs.length_le
    have ht : t <+: branchPrefix x n := by
      rw [← hx]
      exact branchPrefix_mono x (hlen ▸ hsn)
    exact hne ((List.prefix_of_prefix_length_le hs ht hlen.le).eq_of_length hlen)
  rw [family, ContinuousLinearMap.map_tsum _ (summable_term x)]
  have he (n : ℕ) : projection s (term x n) = 0 := by
    simp [term, projection, maskCLM_single, attached, hn n]
  simp only [he, tsum_zero]

def packet {m : ℕ} (a : Fin m → ℝ) (u : Fin m → Parameter) : Hilbert :=
  ∑ i, a i • family (u i)

theorem packet_coordinate {m : ℕ} (a : Fin m → ℝ) (u : Fin m → Parameter)
    (c : Coordinate) : packet a u c = ∑ i, a i * family (u i) c := by
  change (lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 c) (packet a u) = _
  simp only [packet, map_sum, map_smul, RingHom.id_apply]
  rfl

theorem packet_h_coordinate {m L : ℕ} (S : Fin m → Node)
    (hS : Function.Injective S) (hL : ∀ i, (S i).length = L)
    (a : Fin m → ℝ) (u : Fin m → Parameter)
    (hu : ∀ i, branchPrefix (u i) L = S i) (i : Fin m) :
    packet a u (Sum.inl (S i)) = a i * weight (S i) := by
  rw [packet_coordinate]
  simp [family_h_coordinate, hL i, hu, hS.eq_iff]

theorem packet_projection {m L : ℕ} (S : Fin m → Node)
    (hS : Function.Injective S) (hL : ∀ i, (S i).length = L)
    (a : Fin m → ℝ) (u : Fin m → Parameter)
    (hu : ∀ i, branchPrefix (u i) L = S i) (i : Fin m) :
    projection (S i) (packet a u) = a i • projection (S i) (family (u i)) := by
  rw [packet, map_sum]
  simp only [map_smul]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [projection_family_other (S i) (S j) (u j)
      ((hL i).trans (hL j).symm) (fun h => hji (hS h).symm) (by simpa [hL j] using hu j)]
    simp
  · simp

def coefficient (s : Node) (v : Hilbert) : ℝ := v (Sum.inl s) / weight s

theorem continuous_coefficient (s : Node) : Continuous (coefficient s) :=
  (lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 (Sum.inl s)).continuous.div_const _

theorem coefficient_packet {m L : ℕ} (S : Fin m → Node)
    (hS : Function.Injective S) (hL : ∀ i, (S i).length = L)
    (a : Fin m → ℝ) (u : Fin m → Parameter)
    (hu : ∀ i, branchPrefix (u i) L = S i) (i : Fin m) :
    coefficient (S i) (packet a u) = a i := by
  rw [coefficient, packet_h_coordinate S hS hL a u hu i]
  exact mul_div_cancel_right₀ _ (weight_pos _).ne'

def coefficientBand (k : ℕ) : Set ℝ := {a | 1 / ((k : ℝ) + 1) ≤ |a| ∧ |a| ≤ (k : ℝ) + 1}

theorem isClosed_coefficientBand (k : ℕ) : IsClosed (coefficientBand k) :=
  (isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const)

theorem coefficientBand_ne_zero {k : ℕ} {a : ℝ} (ha : a ∈ coefficientBand k) : a ≠ 0 := by
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  intro h
  have := ha.1
  simp only [h, abs_zero] at this
  linarith

def chart {m : ℕ} (S : Fin m → Node) (k : ℕ) : Set Hilbert :=
  {v | ∃ (a : Fin m → ℝ) (u : Fin m → Parameter),
    (∀ i, a i ∈ coefficientBand k) ∧
    (∀ i, u i ∈ cylinder (S i)) ∧ v = packet a u}

theorem isClosed_chart {m L : ℕ} (S : Fin m → Node)
    (hS : Function.Injective S) (hL : ∀ i, (S i).length = L) (k : ℕ) :
    IsClosed (chart S k) := by
  apply IsSeqClosed.isClosed
  intro v z hv hz
  choose a u ha hu hpacket using hv
  have hprefix (n : ℕ) (i : Fin m) : branchPrefix (u n i) L = S i := by
    simpa [hL i] using (mem_cylinder_iff (S i) _).1 (hu n i)
  let az : Fin m → ℝ := fun i => coefficient (S i) z
  have haconv (i : Fin m) : Tendsto (fun n => a n i) atTop (𝓝 (az i)) := by
    have he : (fun n => a n i) = fun n => coefficient (S i) (v n) := by
      funext n
      rw [hpacket n, coefficient_packet S hS hL (a n) (u n) (hprefix n) i]
    rw [he]
    exact (continuous_coefficient (S i)).continuousAt.tendsto.comp hz
  have haz (i : Fin m) : az i ∈ coefficientBand k :=
    (isClosed_coefficientBand k).mem_of_tendsto (haconv i)
      (Eventually.of_forall (fun n => ha n i))
  have htailconv (i : Fin m) :
      Tendsto (fun n => projection (S i) (family (u n i))) atTop
        (𝓝 ((az i)⁻¹ • projection (S i) z)) := by
    have hn : az i ≠ 0 := coefficientBand_ne_zero (haz i)
    have hraw := ((haconv i).inv₀ hn).smul ((projection (S i)).continuous.continuousAt.tendsto.comp hz)
    convert hraw using 1
    funext n
    change projection (S i) (family (u n i)) = (a n i)⁻¹ • projection (S i) (v n)
    rw [hpacket n, packet_projection S hS hL (a n) (u n) (hprefix n) i]
    simp only [smul_smul, inv_mul_cancel₀ (coefficientBand_ne_zero (ha n i)), one_smul]
  have htailmem (i : Fin m) : ∃ x ∈ cylinder (S i),
      projection (S i) (family x) = (az i)⁻¹ • projection (S i) z := by
    have hm := (isClosed_tailImage (S i)).mem_of_tendsto (htailconv i)
      (Eventually.of_forall (fun n => ⟨family (u n i), ⟨u n i, hu n i, rfl⟩, rfl⟩))
    obtain ⟨w, ⟨x, hx, rfl⟩, hw⟩ := hm
    exact ⟨x, hx, hw⟩
  choose uz huz huzEq using htailmem
  have hfamilyconv (i : Fin m) : Tendsto (fun n => family (u n i)) atTop (𝓝 (family (uz i))) := by
    have hpz : branchPrefix (uz i) (S i).length = S i := (mem_cylinder_iff _ _).1 (huz i)
    have he (n : ℕ) : family (u n i) = prefixPart (uz i) (S i).length +
        projection (S i) (family (u n i)) := by
      nth_rw 1 [family_eq_prefixPart_add_projection (S i) (u n i) ((mem_cylinder_iff _ _).1 (hu n i))]
      rw [prefixPart_eq (u n i) (uz i) (S i).length
        (((mem_cylinder_iff _ _).1 (hu n i)).trans hpz.symm)]
    have hc : Tendsto (fun _ : ℕ => prefixPart (uz i) (S i).length) atTop
        (𝓝 (prefixPart (uz i) (S i).length)) := tendsto_const_nhds
    have h := hc.add (htailconv i)
    rw [← huzEq i] at h
    rw [family_eq_prefixPart_add_projection (S i) (uz i) hpz]
    exact h.congr' (Eventually.of_forall (fun n => (he n).symm))
  have hpacketconv : Tendsto (fun n => packet (a n) (u n)) atTop (𝓝 (packet az uz)) := by
    exact tendsto_finset_sum _ (fun i _ => (haconv i).smul (hfamilyconv i))
  have hzpacket : z = packet az uz := by
    apply tendsto_nhds_unique hz
    exact hpacketconv.congr' (Eventually.of_forall (fun n => (hpacket n).symm))
  exact ⟨az, uz, haz, huz, hzpacket⟩

theorem exists_separating_depth {m : ℕ} (u : Fin m → Parameter)
    (hu : Function.Injective u) : ∃ L : ℕ, Function.Injective (fun i => branchPrefix (u i) L) := by
  have hevent (i j : Fin m) : ∀ᶠ L : ℕ in atTop,
      branchPrefix (u i) L = branchPrefix (u j) L → i = j := by
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ _ => hij)
    have huij : u i ≠ u j := fun h => hij (hu h)
    obtain ⟨n, hn⟩ := Function.ne_iff.mp huij
    filter_upwards [eventually_ge_atTop (n + 1)] with L hL hprefix
    have hcoords := List.ofFn_injective hprefix
    exact (hn (congrFun hcoords ⟨n, by omega⟩)).elim
  have h : ∀ᶠ L : ℕ in atTop, ∀ i j, branchPrefix (u i) L = branchPrefix (u j) L → i = j :=
    Filter.eventually_all.2 (fun i => Filter.eventually_all.2 (hevent i))
  exact h.exists

theorem exists_coefficientBand {m : ℕ} (a : Fin m → ℝ) (ha : ∀ i, a i ≠ 0) :
    ∃ k : ℕ, ∀ i, a i ∈ coefficientBand k := by
  obtain ⟨k, hk⟩ := exists_nat_gt (∑ i, (|a i| + |a i|⁻¹))
  refine ⟨k, fun i => ?_⟩
  have hsum : |a i| + |a i|⁻¹ ≤ ∑ j, (|a j| + |a j|⁻¹) :=
    Finset.single_le_sum (f := fun j : Fin m => |a j| + |a j|⁻¹)
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hpos : 0 < |a i| := abs_pos.2 (ha i)
  have hinv : |a i|⁻¹ ≤ (k : ℝ) + 1 := by linarith [inv_nonneg.2 hpos.le]
  have hmul := mul_le_mul_of_nonneg_right hinv hpos.le
  rw [inv_mul_cancel₀ hpos.ne'] at hmul
  constructor
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)).2
    nlinarith
  · linarith [inv_nonneg.2 hpos.le]

theorem exists_packet_of_mem_span {v : Hilbert} (hv : v ∈ span) :
    ∃ (m : ℕ) (a : Fin m → ℝ) (u : Fin m → Parameter),
      (∀ i, a i ≠ 0) ∧ Function.Injective u ∧ v = packet a u := by
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hv
  let e : Fin (Fintype.card c.support) ≃ c.support := (Fintype.equivFin c.support).symm
  let u : Fin (Fintype.card c.support) → Parameter := fun i => e i
  let a : Fin (Fintype.card c.support) → ℝ := fun i => c (u i)
  refine ⟨_, a, u, (fun i => Finsupp.mem_support_iff.1 (e i).property),
    Subtype.val_injective.comp e.injective, ?_⟩
  rw [← hc]
  symm
  change (∑ i, c (u i) • family (u i)) = c.sum (fun i a => a • family i)
  calc
    _ = ∑ i : c.support, c i • family i := Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Finsupp.sum]
      apply Finset.sum_bij (fun i _ => i.val)
      · intro i _; exact i.property
      · intro i _ j _ hij; exact Subtype.ext hij
      · intro x hx; exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩
      · intro _ _; rfl

theorem mem_span_iff_mem_chart (v : Hilbert) : v ∈ span ↔
    ∃ (m L : ℕ) (S : Fin m → Node) (k : ℕ),
      Function.Injective S ∧ (∀ i, (S i).length = L) ∧ v ∈ chart S k := by
  constructor
  · intro hv
    obtain ⟨m, a, u, ha, hu, hpacket⟩ := exists_packet_of_mem_span hv
    obtain ⟨L, hL⟩ := exists_separating_depth u hu
    obtain ⟨k, hk⟩ := exists_coefficientBand a ha
    refine ⟨m, L, (fun i => branchPrefix (u i) L), k, hL,
      (fun _ => length_prefix _ _), a, u, hk, ?_, hpacket⟩
    intro i
    apply (mem_cylinder_iff _ _).2
    simp
  · rintro ⟨m, L, S, k, _, _, a, u, _, _, rfl⟩
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (family_mem_span (u i)))

abbrev ChartIndex := Σ m : ℕ, ℕ × (Fin m → Node) × ℕ

def closedChart (I : ChartIndex) : Set Hilbert :=
  if h : Function.Injective I.2.2.1 ∧ (∀ i, (I.2.2.1 i).length = I.2.1) then
    chart I.2.2.1 I.2.2.2 else ∅

theorem isClosed_closedChart (I : ChartIndex) : IsClosed (closedChart I) := by
  unfold closedChart
  split_ifs with h
  · exact isClosed_chart _ h.1 h.2 _
  · exact isClosed_empty

theorem isFSigma_span : IsFSigma (span : Set Hilbert) := by
  classical
  letI : Encodable ChartIndex := Encodable.ofCountable ChartIndex
  let C : ℕ → Set Hilbert := fun n => match Encodable.decode (α := ChartIndex) n with
    | some I => closedChart I
    | none => ∅
  have hC (n : ℕ) : IsClosed (C n) := by
    dsimp [C]
    split <;> simp_all only [isClosed_closedChart, isClosed_empty]
  refine ⟨C, hC, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨m, L, S, k, hS, hL, hv⟩ := (mem_span_iff_mem_chart v).1 hv
    refine Set.mem_iUnion.2 ⟨Encodable.encode (⟨m, L, S, k⟩ : ChartIndex), ?_⟩
    simpa only [C, Encodable.encodek, closedChart,
      dif_pos (show Function.Injective S ∧ (∀ i, (S i).length = L) from ⟨hS, hL⟩)] using hv
  · intro hv
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hv
    cases he : Encodable.decode (α := ChartIndex) n with
    | none => simpa [C, he] using hn
    | some I =>
      have hmem : v ∈ closedChart I := by simpa [C, he] using hn
      unfold closedChart at hmem
      split_ifs at hmem with h
      · exact (mem_span_iff_mem_chart v).2 ⟨I.1, I.2.1, I.2.2.1, I.2.2.2, h.1, h.2, hmem⟩
      · exact hmem.elim

theorem branchPrefix_eq_of_le (x y : Parameter) {m n : ℕ} (hmn : m ≤ n)
    (h : branchPrefix x n = branchPrefix y n) : branchPrefix x m = branchPrefix y m := by
  apply congrArg List.ofFn
  funext i
  exact congrFun (List.ofFn_injective h) ⟨i, Nat.lt_of_lt_of_le i.isLt hmn⟩

theorem eq_zero_of_mem_span_bounded_depth {v : Hilbert} (hv : v ∈ span) (N : ℕ)
    (hbound : ∀ c : Coordinate, N < (attached c).length → v c = 0) : v = 0 := by
  obtain ⟨m, a, u, ha, hu, hpacket⟩ := exists_packet_of_mem_span hv
  by_cases hm : m = 0
  · subst m
    simpa [packet] using hpacket
  obtain ⟨L₀, hL₀⟩ := exists_separating_depth u hu
  let L := max L₀ (N + 1)
  have hL : Function.Injective (fun i => branchPrefix (u i) L) := by
    intro i j he
    exact hL₀ (branchPrefix_eq_of_le (u i) (u j) (le_max_left _ _) he)
  let i : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have he := hbound (Sum.inl (branchPrefix (u i) L)) (by
    simp only [attached, Sum.elim_inl, id_eq, length_prefix]
    exact lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _))
  rw [hpacket, packet_h_coordinate (fun i => branchPrefix (u i) L) hL
    (fun _ => length_prefix _ _) a u (fun _ => rfl) i] at he
  exact (mul_ne_zero (ha i) (weight_pos _).ne' he).elim

theorem term_apply_zero_of_depth_ne (x : Parameter) (n : ℕ) (c : Coordinate)
    (h : (attached c).length ≠ n) : term x n c = 0 := by
  rw [term_apply]
  have hh : c ≠ Sum.inl (branchPrefix x n) := by
    intro he
    apply h
    simp [he, attached]
  have he : c ≠ Sum.inr (branchPrefix x n, x n / 2) := by
    intro he
    apply h
    simp [he, attached]
  simp [Pi.single_eq_of_ne hh, Pi.single_eq_of_ne he]

theorem prefixPart_apply (x : Parameter) (L : ℕ) (c : Coordinate) :
    prefixPart x L c = ∑ n ∈ Finset.range L, term x n c := by
  change (lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 c) (prefixPart x L) = _
  simp only [prefixPart, map_sum]
  rfl

theorem prefixPart_apply_zero_of_depth_ge (x : Parameter) (L : ℕ) (c : Coordinate)
    (h : L ≤ (attached c).length) : prefixPart x L c = 0 := by
  rw [prefixPart_apply]
  apply Finset.sum_eq_zero
  intro n hn
  apply term_apply_zero_of_depth_ne
  have := Finset.mem_range.1 hn
  omega

end NoUniversalFSigma.Branch
end
end

/- Source module: NoUniversalFSigma.BranchEscape -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open Set Filter Topology
namespace NoUniversalFSigma.Branch

theorem isOpen_cylinder (s : Node) : IsOpen (cylinder s) := by
  change IsOpen {x : Parameter | ∀ i : Fin s.length, x i = s[i]}
  simp only [setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  change IsOpen ((fun x : Parameter => x (i : ℕ)) ⁻¹' {s[i]})
  exact (isOpen_discrete ({s[i]} : Set ℕ)).preimage
    (show Continuous (fun x : Parameter => x (i : ℕ)) from continuous_apply _)

def separator (s : Node) : Hilbert →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : Coordinate => ℝ) 2 (Sum.inl s)

theorem separator_family (s : Node) (x : Parameter) :
    separator s (family x) = if x ∈ cylinder s then weight s else 0 := by
  change family x (Sum.inl s) = _
  simp only [family_h_coordinate, mem_cylinder_iff]

theorem isLocallyConstant_separator (s : Node) :
    IsLocallyConstant (fun x => separator s (family x)) := by
  apply (IsLocallyConstant.iff_exists_open _).2
  intro x
  by_cases hx : x ∈ cylinder s
  · refine ⟨cylinder s, isOpen_cylinder s, hx, fun y hy => ?_⟩
    simp only [separator_family, if_pos hx, if_pos hy]
  · refine ⟨(cylinder s)ᶜ, (isClosed_cylinder s).isOpen_compl, hx, fun y hy => ?_⟩
    simp only [separator_family, if_neg hx, if_neg hy]

theorem separators_separate {x y : Parameter} (h : x ≠ y) :
    ∃ s : Node, separator s (family x) ≠ separator s (family y) := by
  obtain ⟨n, hn⟩ := Function.ne_iff.mp h
  let s := branchPrefix x (n + 1)
  have hy : branchPrefix y s.length ≠ s := by
    intro he
    have hlen : s.length = n + 1 := length_prefix _ _
    rw [hlen] at he
    exact hn (congrFun (List.ofFn_injective he.symm) ⟨n, Nat.lt_succ_self n⟩)
  refine ⟨s, ?_⟩
  change family x (Sum.inl s) ≠ family y (Sum.inl s)
  rw [family_h_coordinate, family_h_coordinate, if_neg hy]
  have hx : branchPrefix x s.length = s := by simp [s]
  rw [if_pos hx]
  exact (weight_pos s).ne'

def separatingFunctionals (n : ℕ) : Hilbert →L[ℝ] ℝ :=
  match Encodable.decode (α := Node) n with
  | some s => separator s
  | none => separator []

theorem separatingFunctionals_locallyConstant (n : ℕ) :
    IsLocallyConstant (fun x => separatingFunctionals n (family x)) := by
  unfold separatingFunctionals
  split <;> exact isLocallyConstant_separator _

theorem separatingFunctionals_separate {x y : Parameter} (h : x ≠ y) :
    ∃ n : ℕ, separatingFunctionals n (family x) ≠ separatingFunctionals n (family y) := by
  obtain ⟨s, hs⟩ := separators_separate h
  exact ⟨Encodable.encode s, by simpa only [separatingFunctionals, Encodable.encodek] using hs⟩

theorem norm_term_le_weight (x : Parameter) (n : ℕ) :
    ‖term x n‖ ≤ 2 * weight (branchPrefix x n) := by
  rw [term, norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos _)]
  calc
    _ ≤ weight (branchPrefix x n) *
        (‖(lp.single 2 (Sum.inl (branchPrefix x n)) (1 : ℝ) : Hilbert)‖ +
         ‖(lp.single 2 (Sum.inr (branchPrefix x n, x n / 2)) ((-1 : ℝ) ^ x n) : Hilbert)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (weight_pos _).le
    _ = _ := by rw [lp.norm_single (by norm_num), lp.norm_single (by norm_num)]; simp; ring

theorem weight_step_le (x : Parameter) (n : ℕ) :
    weight (branchPrefix x (n + 1)) ≤ weight (branchPrefix x n) * (1 / 4 : ℝ) := by
  rw [branchPrefix_succ, weight_append]
  apply mul_le_mul_of_nonneg_left _ (weight_pos _).le
  have h : (1 / 2 : ℝ) ^ (x n + 2) ≤ (1 / 2 : ℝ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h ⊢
  exact h

theorem weight_tail_le (x : Parameter) (L n : ℕ) :
    weight (branchPrefix x (n + L)) ≤ weight (branchPrefix x L) * (1 / 4 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = weight (branchPrefix x ((n + L) + 1)) := by congr 2 <;> omega
      _ ≤ weight (branchPrefix x (n + L)) * (1 / 4 : ℝ) := weight_step_le _ _
      _ ≤ (weight (branchPrefix x L) * (1 / 4 : ℝ) ^ n) * (1 / 4 : ℝ) := by gcongr
      _ = _ := by rw [pow_succ]; ring

def tailSeries (x : Parameter) (L : ℕ) : Hilbert := ∑' n : ℕ, term x (n + L)

theorem norm_tailSeries_le (x : Parameter) (L : ℕ) :
    ‖tailSeries x L‖ ≤ (8 / 3 : ℝ) * weight (branchPrefix x L) := by
  have hbound (n : ℕ) : ‖term x (n + L)‖ ≤
      (2 * weight (branchPrefix x L)) * (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ 2 * weight (branchPrefix x (n + L)) := norm_term_le_weight _ _
      _ ≤ 2 * (weight (branchPrefix x L) * (1 / 4 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left (weight_tail_le x L n) (by norm_num)
      _ = _ := by ring
  have h := tsum_of_norm_bounded
    ((hasSum_geometric_of_abs_lt_one (by norm_num : |(1 / 4 : ℝ)| < 1)).mul_left
      (2 * weight (branchPrefix x L))) hbound
  norm_num [tailSeries] at h ⊢
  convert h using 1 <;> ring

theorem family_eq_prefixPart_add_tail (x : Parameter) (L : ℕ) :
    family x = prefixPart x L + tailSeries x L :=
  ((summable_term x).sum_add_tsum_nat_add L).symm

def continuation (s : Node) (k : ℕ) : Parameter := fun n =>
  if h : n < s.length then s[n] else if n = s.length then k else 0

theorem continuation_mem_cylinder (s : Node) (k : ℕ) : continuation s k ∈ cylinder s := by
  intro i
  simp [continuation, i.isLt]

@[simp] theorem continuation_prefix (s : Node) (k : ℕ) :
    branchPrefix (continuation s k) s.length = s :=
  (mem_cylinder_iff s _).1 (continuation_mem_cylinder s k)

@[simp] theorem continuation_digit (s : Node) (k : ℕ) : continuation s k s.length = k := by
  simp [continuation]

@[simp] theorem continuation_prefix_succ (s : Node) (k : ℕ) :
    branchPrefix (continuation s k) (s.length + 1) = s ++ [k] := by
  rw [branchPrefix_succ, continuation_prefix, continuation_digit]

theorem continuation_term (s : Node) (k : ℕ) : term (continuation s k) s.length =
    weight s • ((lp.single 2 (Sum.inl s) (1 : ℝ) : Hilbert) +
      lp.single 2 (Sum.inr (s, k / 2)) ((-1 : ℝ) ^ k)) := by
  simp only [term, continuation_prefix, continuation_digit]

theorem continuation_paired_terms (s : Node) (n : ℕ) :
    term (continuation s (2 * n)) s.length + term (continuation s (2 * n + 1)) s.length =
      (2 * weight s) • (lp.single 2 (Sum.inl s) (1 : ℝ) : Hilbert) := by
  have he : (2 * n) / 2 = n := by omega
  have ho : (2 * n + 1) / 2 = n := by omega
  have hp : (-1 : ℝ) ^ (2 * n) = 1 := by rw [pow_mul]; norm_num
  have hm : (-1 : ℝ) ^ (2 * n + 1) = -1 := by rw [pow_add, hp]; norm_num
  rw [continuation_term, continuation_term, he, ho, hp, hm]
  have hneg : (lp.single 2 (Sum.inr (s, n)) (-1 : ℝ) : Hilbert) =
      -(lp.single 2 (Sum.inr (s, n)) (1 : ℝ) : Hilbert) := lp.single_neg _ _ _
  rw [hneg]
  module

def escapeVector (s : Node) : Hilbert :=
  (2 : ℝ) • prefixPart (continuation s 0) s.length +
    (2 * weight s) • (lp.single 2 (Sum.inl s) (1 : ℝ) : Hilbert)

theorem escapeVector_h (s : Node) : escapeVector s (Sum.inl s) = 2 * weight s := by
  have hp : prefixPart (continuation s 0) s.length (Sum.inl s) = 0 :=
    prefixPart_apply_zero_of_depth_ge _ _ _ (by simp [attached])
  change 2 * prefixPart (continuation s 0) s.length (Sum.inl s) +
    (2 * weight s) * (lp.single 2 (Sum.inl s) (1 : ℝ) : Hilbert) (Sum.inl s) = _
  rw [hp]
  simp

theorem escapeVector_bounded_depth (s : Node) (c : Coordinate)
    (hc : s.length < (attached c).length) : escapeVector s c = 0 := by
  have hp : prefixPart (continuation s 0) s.length c = 0 :=
    prefixPart_apply_zero_of_depth_ge _ _ _ hc.le
  have hne : c ≠ Sum.inl s := by
    intro he
    simp [he, attached] at hc
  change 2 * prefixPart (continuation s 0) s.length c +
    (2 * weight s) * (lp.single 2 (Sum.inl s) (1 : ℝ) : Hilbert) c = _
  simp [hp, lp.single_apply, Pi.single_eq_of_ne hne]

theorem escapeVector_not_mem_span (s : Node) : escapeVector s ∉ span := by
  intro hs
  have he := eq_zero_of_mem_span_bounded_depth hs s.length (escapeVector_bounded_depth s)
  have hc := congrArg (fun v : Hilbert => v (Sum.inl s)) he
  change escapeVector s (Sum.inl s) = 0 at hc
  rw [escapeVector_h] at hc
  have := weight_pos s
  linarith

theorem continuation_pair_identity (s : Node) (n : ℕ) :
    family (continuation s (2 * n)) + family (continuation s (2 * n + 1)) =
      escapeVector s + tailSeries (continuation s (2 * n)) (s.length + 1) +
        tailSeries (continuation s (2 * n + 1)) (s.length + 1) := by
  rw [family_eq_prefixPart_add_tail _ (s.length + 1),
    family_eq_prefixPart_add_tail _ (s.length + 1)]
  have hprefix (k : ℕ) : prefixPart (continuation s k) s.length =
      prefixPart (continuation s 0) s.length :=
    prefixPart_eq _ _ _ (by rw [continuation_prefix, continuation_prefix])
  have hsucc (x : Parameter) : prefixPart x (s.length + 1) =
      prefixPart x s.length + term x s.length := Finset.sum_range_succ _ _
  rw [hsucc, hsucc]
  simp only [hprefix]
  have hp := continuation_paired_terms s n
  dsimp [escapeVector]
  calc
    _ = (2 : ℝ) • prefixPart (continuation s 0) s.length +
        (term (continuation s (2 * n)) s.length + term (continuation s (2 * n + 1)) s.length) +
        tailSeries (continuation s (2 * n)) (s.length + 1) +
        tailSeries (continuation s (2 * n + 1)) (s.length + 1) := by module
    _ = _ := by rw [hp]

theorem continuation_tail_tendsto_zero (s : Node) (k : ℕ → ℕ)
    (hk : ∀ n, n ≤ k n + 2) :
    Tendsto (fun n => tailSeries (continuation s (k n)) (s.length + 1)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hbound (n : ℕ) : ‖tailSeries (continuation s (k n)) (s.length + 1)‖ ≤
      ((8 / 3 : ℝ) * weight s) * (1 / 2 : ℝ) ^ n := by
    calc
      _ ≤ (8 / 3 : ℝ) * weight (branchPrefix (continuation s (k n)) (s.length + 1)) :=
        norm_tailSeries_le _ _
      _ = ((8 / 3 : ℝ) * weight s) * (1 / 2 : ℝ) ^ (k n + 2) := by
        rw [continuation_prefix_succ, weight_append]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity [weight_pos s])
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hk n)
  have hgeom : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit := hgeom.const_mul ((8 / 3 : ℝ) * weight s)
  simp only [mul_zero] at hlimit
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hlimit

theorem continuation_pair_tendsto (s : Node) :
    Tendsto (fun n => family (continuation s (2 * n)) + family (continuation s (2 * n + 1)))
      atTop (𝓝 (escapeVector s)) := by
  have hc : Tendsto (fun _ : ℕ => escapeVector s) atTop (𝓝 (escapeVector s)) := tendsto_const_nhds
  have hx := continuation_tail_tendsto_zero s (fun n => 2 * n) (fun n => by dsimp; omega)
  have hy := continuation_tail_tendsto_zero s (fun n => 2 * n + 1) (fun n => by dsimp; omega)
  have h := (hc.add hx).add hy
  simpa only [add_zero, ← continuation_pair_identity] using h

theorem cylinder_branchPrefix (x : Parameter) (L : ℕ) :
    cylinder (branchPrefix x L) = PiNat.cylinder x L := by
  ext y
  rw [mem_cylinder_iff, length_prefix, PiNat.mem_cylinder_iff]
  constructor
  · intro h i hi
    exact congrFun (List.ofFn_injective h) ⟨i, hi⟩
  · intro h
    exact congrArg List.ofFn (funext (fun i => h i i.isLt))

theorem exists_cylinder_square_subset (t : Parameter) (U : Set (Parameter × Parameter))
    (hU : IsOpen U) (ht : (t, t) ∈ U) :
    ∃ s : Node, (cylinder s ×ˢ cylinder s) ⊆ U := by
  obtain ⟨A, B, hA, htA, hB, htB, hAB⟩ := mem_nhds_prod_iff'.1 (hU.mem_nhds ht)
  obtain ⟨V, ⟨x, L, rfl⟩, _, hV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open
      (show t ∈ A ∩ B from ⟨htA, htB⟩) (hA.inter hB)
  refine ⟨branchPrefix x L, ?_⟩
  rw [cylinder_branchPrefix]
  exact (Set.prod_mono (fun _ hy => (hV hy).1) (fun _ hy => (hV hy).2)).trans hAB

theorem diagonal_mem_escapeDerivative (t : Parameter) :
    (t, t) ∈ escapeDerivative (span : Set Hilbert) family Set.univ := by
  refine ⟨Set.mem_univ _, ?_⟩
  intro U hU ht hsub
  obtain ⟨s, hs⟩ := exists_cylinder_square_subset t U hU ht
  have hmem : escapeVector s ∈ closure (pairSum family '' (Set.univ ∩ U)) := by
    apply isClosed_closure.mem_of_tendsto (continuation_pair_tendsto s)
    apply Eventually.of_forall
    intro n
    apply subset_closure
    exact ⟨(continuation s (2 * n), continuation s (2 * n + 1)),
      ⟨Set.mem_univ _, hs ⟨continuation_mem_cylinder s _, continuation_mem_cylinder s _⟩⟩, rfl⟩
  exact escapeVector_not_mem_span s (hsub hmem)

theorem diagonal_rank_one (t : Parameter) :
    (t, t) ∈ escapeRemainder (span : Set Hilbert) family 1 := by
  rw [show (1 : Ordinal) = 0 + 1 by simp, escapeRemainder_succ, escapeRemainder_zero]
  exact diagonal_mem_escapeDerivative t

end NoUniversalFSigma.Branch
end
end

/- Source module: NoUniversalFSigma.Successor -/
section
noncomputable section
open Set

namespace NoUniversalFSigma

universe u v w z
variable {P : Type u} {Q : Type v} {B : Type w} {C : Type z}

/-- The additive product of two parameter families. -/
def productFamily (j : P → B) (k : Q → C) : P × Q → B × C :=
  fun p => (j p.1, k p.2)

section Algebra
variable [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]

/-- The algebraic span of a mass-one product family is the mass-matched product
of the two algebraic spans. -/
theorem mem_span_productFamily_iff [Nonempty P] [Nonempty Q]
    (j : P → B) (k : Q → C) (ρ : B →ₗ[ℝ] ℝ) (σ : C →ₗ[ℝ] ℝ)
    (hj : ∀ p, ρ (j p) = 1) (hk : ∀ q, σ (k q) = 1) (v : B × C) :
    v ∈ Submodule.span ℝ (range (productFamily j k)) ↔
      v.1 ∈ Submodule.span ℝ (range j) ∧
      v.2 ∈ Submodule.span ℝ (range k) ∧ ρ v.1 = σ v.2 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨p, q⟩, rfl⟩ := hv
      exact ⟨Submodule.subset_span (mem_range_self p),
        Submodule.subset_span (mem_range_self q), by simp [productFamily, hj, hk]⟩
    | zero => simp
    | add x y hx hy IHx IHy =>
      exact ⟨Submodule.add_mem _ IHx.1 IHy.1, Submodule.add_mem _ IHx.2.1 IHy.2.1,
        by simp only [Prod.fst_add, Prod.snd_add, map_add, IHx.2.2, IHy.2.2]⟩
    | smul a x hx IH =>
      exact ⟨Submodule.smul_mem _ a IH.1, Submodule.smul_mem _ a IH.2.1,
        by change ρ (a • x.1) = σ (a • x.2); simp only [map_smul, IH.2.2]⟩
  · rintro ⟨hv, hw, hmass⟩
    let p₀ : P := Classical.choice inferInstance
    let q₀ : Q := Classical.choice inferInstance
    let M := Submodule.span ℝ (range (productFamily j k))
    have hleft : ∀ b ∈ Submodule.span ℝ (range j), (b, ρ b • k q₀) ∈ M := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨p, rfl⟩ := hb
        simpa [hj] using (Submodule.subset_span (mem_range_self (p, q₀)) :
          productFamily j k (p, q₀) ∈ M)
      | zero => simpa only [map_zero, zero_smul] using M.zero_mem
      | add x y hx hy IHx IHy =>
        simpa only [map_add, add_smul, Prod.mk_add_mk] using M.add_mem IHx IHy
      | smul a x hx IH =>
        simpa only [map_smul, smul_smul, Prod.smul_mk] using M.smul_mem a IH
    have hright : ∀ c ∈ Submodule.span ℝ (range k), (σ c • j p₀, c) ∈ M := by
      intro c hc
      induction hc using Submodule.span_induction with
      | mem c hc =>
        obtain ⟨q, rfl⟩ := hc
        simpa [hk] using (Submodule.subset_span (mem_range_self (p₀, q)) :
          productFamily j k (p₀, q) ∈ M)
      | zero => simpa only [map_zero, zero_smul] using M.zero_mem
      | add x y hx hy IHx IHy =>
        simpa only [map_add, add_smul, Prod.mk_add_mk] using M.add_mem IHx IHy
      | smul a x hx IH =>
        simpa only [map_smul, smul_smul, Prod.smul_mk] using M.smul_mem a IH
    have hbase : productFamily j k (p₀, q₀) ∈ M :=
      Submodule.subset_span (mem_range_self _)
    have h := M.sub_mem (M.add_mem (hleft v.1 hv) (hright v.2 hw))
      (M.smul_mem (ρ v.1) hbase)
    convert h using 1
    ext <;> simp [productFamily, hmass]

end Algebra

section Topology
variable [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace B] [TopologicalSpace C]

theorem continuous_productFamily {j : P → B} {k : Q → C}
    (hj : Continuous j) (hk : Continuous k) : Continuous (productFamily j k) :=
  hj.prodMap hk

theorem isClosedEmbedding_productFamily {j : P → B} {k : Q → C}
    (hj : Topology.IsClosedEmbedding j) (hk : Topology.IsClosedEmbedding k) :
    Topology.IsClosedEmbedding (productFamily j k) :=
  hj.prodMap hk

end Topology

section Normed
variable [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]

omit [NormedSpace ℝ B] [NormedSpace ℝ C] in
theorem norm_productFamily_le (j : P → B) (k : Q → C) {b c : ℝ}
    (hj : ∀ p, ‖j p‖ ≤ b) (hk : ∀ q, ‖k q‖ ≤ c) (p : P × Q) :
    ‖productFamily j k p‖ ≤ max b c := by
  exact max_le_max (hj p.1) (hk p.2)

theorem isFSigma_span_productFamily [Nonempty P] [Nonempty Q]
    (j : P → B) (k : Q → C) (ρ : B →L[ℝ] ℝ) (σ : C →L[ℝ] ℝ)
    (hj : ∀ p, ρ (j p) = 1) (hk : ∀ q, σ (k q) = 1)
    (hH : IsFSigma (Submodule.span ℝ (range j) : Set B))
    (hK : IsFSigma (Submodule.span ℝ (range k) : Set C)) :
    IsFSigma (Submodule.span ℝ (range (productFamily j k)) : Set (B × C)) := by
  have heq : (Submodule.span ℝ (range (productFamily j k)) : Set (B × C)) =
      ((Prod.fst ⁻¹' (Submodule.span ℝ (range j) : Set B)) ∩
        (Prod.snd ⁻¹' (Submodule.span ℝ (range k) : Set C))) ∩
        {v | ρ v.1 = σ v.2} := by
    ext v
    simp only [SetLike.mem_coe, mem_inter_iff, mem_preimage, mem_setOf_eq]
    rw [mem_span_productFamily_iff j k ρ.toLinearMap σ.toLinearMap hj hk]
    tauto
  rw [heq]
  exact ((hH.preimage continuous_fst).inter (hK.preimage continuous_snd)).inter_isClosed
    (isClosed_eq (ρ.continuous.comp continuous_fst) (σ.continuous.comp continuous_snd))

end Normed

end NoUniversalFSigma


namespace NoUniversalFSigma

section EscapeSuccessor
universe u v w
variable {P Q : Type u} {B : Type v} {C : Type w}
variable [TopologicalSpace P] [TopologicalSpace Q]
variable [TopologicalSpace B] [TopologicalSpace C] [Add B] [Add C]

/-- The additive product raises diagonal escape rank by one when the second
factor has diagonal escape rank one. This is the rank argument in Lemma 7.2. -/
theorem diagonal_escape_product_succ
    (j : P → B) (k : Q → C) (H : Set B) (K : Set C) (L : Set (B × C))
    (hleft : L ⊆ Prod.fst ⁻¹' H) (hright : L ⊆ Prod.snd ⁻¹' K)
    (α : Ordinal.{u})
    (hα : ∀ p, (p, p) ∈ escapeRemainder H j α)
    (hbase : ∀ q, (q, q) ∈ escapeRemainder K k 1) :
    ∀ p, (p, p) ∈ escapeRemainder L (productFamily j k) (α + 1) := by
  have hslice : ∀ p s r, ((p, s), (p, r)) ∈
      escapeRemainder L (productFamily j k) α := by
    intro p s r
    have htransfer := escapeRemainder_transfer L H (productFamily j k) j
      (fun t => (t, s)) (fun t => (t, r))
      (continuous_id.prodMk continuous_const) (continuous_id.prodMk continuous_const)
      (fun v => (v, k s + k r)) (continuous_id.prodMk continuous_const)
      (fun _ _ => rfl) (fun z hz hL => hz (hleft hL)) α
    exact htransfer ⟨(p, p), hα p, rfl⟩
  intro p
  rw [escapeRemainder_succ]
  refine ⟨hslice p.1 p.2 p.2, ?_⟩
  intro U hU hpU hbad
  let a : Q → P × Q := fun q => (p.1, q)
  have ha : Continuous a := continuous_const.prodMk continuous_id
  let V : Set (Q × Q) := (Prod.map a a) ⁻¹' U
  have hV : IsOpen V := hU.preimage (ha.prodMap ha)
  have hqV : (p.2, p.2) ∈ V := hpU
  have hq := hbase p.2
  rw [show (1 : Ordinal.{u}) = 0 + 1 by simp, escapeRemainder_succ,
    escapeRemainder_zero] at hq
  apply hq.2 V hV hqV
  intro z hz
  change (j p.1 + j p.1, z) ∈ Prod.snd ⁻¹' K
  apply hright
  apply hbad
  let g : C → B × C := fun z => (j p.1 + j p.1, z)
  have hg : Continuous g := continuous_const.prodMk continuous_id
  have hz' : g z ∈ closure (g '' (pairSum k '' (Set.univ ∩ V))) :=
    image_closure_subset_closure_image hg ⟨z, hz, rfl⟩
  apply closure_mono (s := g '' (pairSum k '' (Set.univ ∩ V))) ?_ hz'
  rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  refine ⟨Prod.map a a q, ⟨hslice p.1 q.1 q.2, hq.2⟩, ?_⟩
  rfl

end EscapeSuccessor
end NoUniversalFSigma

namespace NoUniversalFSigma
section SpanSuccessor
universe u v w
variable {P Q : Type u} {B : Type v} {C : Type w}
variable [TopologicalSpace P] [TopologicalSpace Q]
variable [TopologicalSpace B] [TopologicalSpace C]
variable [AddCommGroup B] [Module ℝ B] [AddCommGroup C] [Module ℝ C]

omit [TopologicalSpace P] [TopologicalSpace Q] [TopologicalSpace B] [TopologicalSpace C] in
theorem span_productFamily_le (j : P → B) (k : Q → C) :
    Submodule.span ℝ (range (productFamily j k)) ≤
      (Submodule.span ℝ (range j)).prod (Submodule.span ℝ (range k)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact ⟨Submodule.subset_span (mem_range_self p.1),
    Submodule.subset_span (mem_range_self p.2)⟩

/-- The successor rank theorem for the actual algebraic spans. -/
theorem diagonal_escape_span_product_succ (j : P → B) (k : Q → C)
    (α : Ordinal.{u})
    (hα : ∀ p, (p, p) ∈ escapeRemainder
      (Submodule.span ℝ (range j) : Set B) j α)
    (hbase : ∀ q, (q, q) ∈ escapeRemainder
      (Submodule.span ℝ (range k) : Set C) k 1) :
    ∀ p, (p, p) ∈ escapeRemainder
      (Submodule.span ℝ (range (productFamily j k)) : Set (B × C))
      (productFamily j k) (α + 1) := by
  exact diagonal_escape_product_succ j k _ _ _
    (fun _ hv => (span_productFamily_le j k hv).1)
    (fun _ hv => (span_productFamily_le j k hv).2) α hα hbase

end SpanSuccessor
end NoUniversalFSigma


namespace NoUniversalFSigma
section LinearTransport
universe u v w
variable {P : Type u} {B : Type v} {C : Type w}
variable [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- Linear homeomorphisms preserve the exact algebraic span of a family. -/
theorem mem_span_equiv_family (e : B ≃L[ℝ] C) (j : P → B) (v : C) :
    v ∈ Submodule.span ℝ (range (e ∘ j)) ↔
      e.symm v ∈ Submodule.span ℝ (range j) := by
  have hrange : range (e ∘ j) = e.toLinearMap '' range j := by
    ext x
    simp only [mem_range, mem_image, Function.comp_apply]
    exact ⟨fun ⟨p, hp⟩ => ⟨j p, ⟨p, rfl⟩, hp⟩,
      fun ⟨b, ⟨p, hp⟩, hb⟩ => ⟨p, hp ▸ hb⟩⟩
  rw [hrange]
  simpa using
    (Submodule.apply_mem_span_image_iff_mem_span
      (f := e.toLinearMap) (x := e.symm v) (s := range j) e.injective)

theorem isFSigma_span_equiv_family (e : B ≃L[ℝ] C) (j : P → B)
    (hH : IsFSigma (Submodule.span ℝ (range j) : Set B)) :
    IsFSigma (Submodule.span ℝ (range (e ∘ j)) : Set C) := by
  have hset : (Submodule.span ℝ (range (e ∘ j)) : Set C) =
      e.symm ⁻¹' (Submodule.span ℝ (range j) : Set B) := by
    ext v
    exact mem_span_equiv_family e j v
  rw [hset]
  exact hH.preimage e.symm.continuous

variable [TopologicalSpace P]

theorem diagonal_escape_equiv_family (e : B ≃L[ℝ] C) (j : P → B)
    (α : Ordinal.{u}) (hα : ∀ p, (p, p) ∈
      escapeRemainder (Submodule.span ℝ (range j) : Set B) j α) :
    ∀ p, (p, p) ∈ escapeRemainder
      (Submodule.span ℝ (range (e ∘ j)) : Set C) (e ∘ j) α := by
  intro p
  have htransfer := escapeRemainder_transfer
    (Submodule.span ℝ (range (e ∘ j)) : Set C)
    (Submodule.span ℝ (range j) : Set B) (e ∘ j) j
    id id continuous_id continuous_id e e.continuous
    (fun t u => (e.map_add (j t) (j u)).symm)
    (fun z hz hmem => hz (by simpa only [e.symm_apply_apply] using
      (mem_span_equiv_family e j (e z)).mp hmem)) α
  exact htransfer ⟨(p, p), hα p, rfl⟩

end LinearTransport
end NoUniversalFSigma


namespace NoUniversalFSigma
section HilbertProduct
universe u v w
variable {P Q : Type u} {B : Type v} {C : Type w}
variable [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The additive product in the genuine Hilbert product norm. -/
def hilbertProductFamily (j : P → B) (k : Q → C) : P × Q → WithLp 2 (B × C) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm ∘ productFamily j k

/-- The inherited mass functional in the Hilbert product. -/
def hilbertProductMass (ρ : B →L[ℝ] ℝ) : WithLp 2 (B × C) →L[ℝ] ℝ :=
  ρ.comp ((ContinuousLinearMap.fst ℝ B C).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ B C).toContinuousLinearMap)

@[simp] theorem hilbertProductMass_family (j : P → B) (k : Q → C)
    (ρ : B →L[ℝ] ℝ) (hj : ∀ p, ρ (j p) = 1) (p : P × Q) :
    hilbertProductMass ρ (hilbertProductFamily j k p) = 1 := hj p.1

theorem norm_hilbertProductFamily_le (j : P → B) (k : Q → C) {b c : ℝ}
    (hj : ∀ p, ‖j p‖ ≤ b) (hk : ∀ q, ‖k q‖ ≤ c) (p : P × Q) :
    ‖hilbertProductFamily j k p‖ ≤
      ‖(WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm.toContinuousLinearMap‖ * max b c := by
  exact ContinuousLinearMap.le_opNorm_of_le
    (WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm.toContinuousLinearMap
    (norm_productFamily_le j k hj hk p)

theorem isFSigma_span_hilbertProductFamily [Nonempty P] [Nonempty Q]
    (j : P → B) (k : Q → C) (ρ : B →L[ℝ] ℝ) (σ : C →L[ℝ] ℝ)
    (hj : ∀ p, ρ (j p) = 1) (hk : ∀ q, σ (k q) = 1)
    (hH : IsFSigma (Submodule.span ℝ (range j) : Set B))
    (hK : IsFSigma (Submodule.span ℝ (range k) : Set C)) :
    IsFSigma (Submodule.span ℝ (range (hilbertProductFamily j k)) :
      Set (WithLp 2 (B × C))) :=
  isFSigma_span_equiv_family (WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm
    (productFamily j k) (isFSigma_span_productFamily j k ρ σ hj hk hH hK)

variable [TopologicalSpace P] [TopologicalSpace Q]

theorem continuous_hilbertProductFamily {j : P → B} {k : Q → C}
    (hj : Continuous j) (hk : Continuous k) : Continuous (hilbertProductFamily j k) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm.continuous.comp
    (continuous_productFamily hj hk)

theorem isClosedEmbedding_hilbertProductFamily {j : P → B} {k : Q → C}
    (hj : Topology.IsClosedEmbedding j) (hk : Topology.IsClosedEmbedding k) :
    Topology.IsClosedEmbedding (hilbertProductFamily j k) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm.toHomeomorph.isClosedEmbedding.comp
    (isClosedEmbedding_productFamily hj hk)

/-- The successor construction with a genuine Hilbert product ambient space. -/
theorem diagonal_escape_hilbertProduct_succ (j : P → B) (k : Q → C)
    (α : Ordinal.{u})
    (hα : ∀ p, (p, p) ∈ escapeRemainder
      (Submodule.span ℝ (range j) : Set B) j α)
    (hbase : ∀ q, (q, q) ∈ escapeRemainder
      (Submodule.span ℝ (range k) : Set C) k 1) :
    ∀ p, (p, p) ∈ escapeRemainder
      (Submodule.span ℝ (range (hilbertProductFamily j k)) : Set (WithLp 2 (B × C)))
      (hilbertProductFamily j k) (α + 1) :=
  diagonal_escape_equiv_family (WithLp.prodContinuousLinearEquiv 2 ℝ B C).symm
    (productFamily j k) (α + 1) (diagonal_escape_span_product_succ j k α hα hbase)

end HilbertProduct
end NoUniversalFSigma


namespace NoUniversalFSigma
section Separators
universe u v w i j
variable {P Q : Type u} {B : Type v} {C : Type w} {I : Type i} {J : Type j}
variable [TopologicalSpace P] [TopologicalSpace Q]
variable [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- The inherited separating linear functionals of the Hilbert product. The
index type is countable whenever the two original index types are countable. -/
def hilbertProductSeparator (ℓ : I → B →L[ℝ] ℝ) (m : J → C →L[ℝ] ℝ) :
    I ⊕ J → WithLp 2 (B × C) →L[ℝ] ℝ :=
  Sum.elim (fun i => (ℓ i).comp (WithLp.fstL 2 ℝ B C))
    (fun j => (m j).comp (WithLp.sndL 2 ℝ B C))

theorem hilbertProductSeparator_locallyConstant
    (j : P → B) (k : Q → C) (ℓ : I → B →L[ℝ] ℝ) (m : J → C →L[ℝ] ℝ)
    (hℓ : ∀ i, IsLocallyConstant (ℓ i ∘ j))
    (hm : ∀ i, IsLocallyConstant (m i ∘ k)) (a : I ⊕ J) :
    IsLocallyConstant (hilbertProductSeparator ℓ m a ∘ hilbertProductFamily j k) := by
  cases a with
  | inl i => exact (hℓ i).comp_continuous continuous_fst
  | inr i => exact (hm i).comp_continuous continuous_snd

omit [TopologicalSpace P] [TopologicalSpace Q] in
theorem hilbertProductSeparator_separates
    (j : P → B) (k : Q → C) (ℓ : I → B →L[ℝ] ℝ) (m : J → C →L[ℝ] ℝ)
    (hℓ : ∀ p q, p ≠ q → ∃ i, ℓ i (j p) ≠ ℓ i (j q))
    (hm : ∀ p q, p ≠ q → ∃ i, m i (k p) ≠ m i (k q)) :
    ∀ p q : P × Q, p ≠ q → ∃ a : I ⊕ J,
      hilbertProductSeparator ℓ m a (hilbertProductFamily j k p) ≠
        hilbertProductSeparator ℓ m a (hilbertProductFamily j k q) := by
  intro p q hpq
  by_cases hp : p.1 = q.1
  · have hq : p.2 ≠ q.2 := fun he => hpq (Prod.ext hp he)
    obtain ⟨i, hi⟩ := hm p.2 q.2 hq
    exact ⟨Sum.inr i, hi⟩
  · obtain ⟨i, hi⟩ := hℓ p.1 q.1 hp
    exact ⟨Sum.inl i, hi⟩

end Separators
end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.L2Coordinates -/
section
noncomputable section

open Set TopologicalSpace
open scoped BigOperators ENNReal

namespace NoUniversalFSigma
namespace L2Coordinates

universe u v

abbrev L2 (I : Type u) := lp (fun _ : I => ℝ) 2
abbrev MatrixL2 (I : Type u) (J : Type v) := L2 (I × J)

variable {I : Type u} {J : Type v}

/-- Countably indexed real Hilbert sequence spaces are separable. -/
instance [Countable I] : SeparableSpace (L2 I) := by
  let b : HilbertBasis I ℝ (L2 I) := default
  have hs : IsSeparable (Submodule.span ℝ (range b) : Set (L2 I)) :=
    (Set.countable_range b).isSeparable.span
  have hc := hs.closure
  have heq : closure (Submodule.span ℝ (range b) : Set (L2 I)) = Set.univ := by
    change ((Submodule.span ℝ (range b)).topologicalClosure : Set (L2 I)) = Set.univ
    rw [b.dense_span]
    rfl
  rw [heq] at hc
  exact isSeparable_univ_iff.mp hc

theorem summable_norm_sq (x : L2 I) : Summable (fun i => ‖x i‖ ^ (2 : ℕ)) := by
  simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

theorem norm_sq (x : L2 I) : ‖x‖ ^ (2 : ℕ) = ∑' i, ‖x i‖ ^ (2 : ℕ) := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) x

/-- Restriction to an injectively indexed family of coordinates. -/
def restrict (e : I → J) (he : Function.Injective e) (x : L2 J) : L2 I :=
  ⟨fun i => x (e i), memℓp_gen (by
    simpa using ((lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).comp_injective he)⟩

@[simp] theorem restrict_apply (e : I → J) (he : Function.Injective e) (x : L2 J) (i : I) :
    restrict e he x i = x (e i) := rfl

theorem norm_restrict_le (e : I → J) (he : Function.Injective e) (x : L2 J) :
    ‖restrict e he x‖ ≤ ‖x‖ := by
  classical
  apply lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg x)
  intro s
  have hsum : ∑ i ∈ s, ‖x (e i)‖ ^ (2 : ℝ≥0∞).toReal =
      ∑ j ∈ s.image e, ‖x j‖ ^ (2 : ℝ≥0∞).toReal := by
    rw [Finset.sum_image]
    exact fun _ _ _ _ h => he h
  change ∑ i ∈ s, ‖x (e i)‖ ^ (2 : ℝ≥0∞).toReal ≤ ‖x‖ ^ (2 : ℝ≥0∞).toReal
  rw [hsum]
  exact lp.sum_rpow_le_norm_rpow (by norm_num) x (s.image e)

def restrictCLM (e : I → J) (he : Function.Injective e) : L2 J →L[ℝ] L2 I :=
  ({ toFun := restrict e he
     map_add' := by intro x y; ext i; rfl
     map_smul' := by intro c x; ext i; rfl } : L2 J →ₗ[ℝ] L2 I).mkContinuous 1
    (by intro x; simpa using norm_restrict_le e he x)

@[simp] theorem restrictCLM_apply (e : I → J) (he : Function.Injective e) (x : L2 J) (i : I) :
    restrictCLM e he x i = x (e i) := rfl

def row (i : I) : MatrixL2 I J →L[ℝ] L2 J :=
  restrictCLM (fun j => (i, j)) (fun _ _ h => (Prod.mk.inj h).2)

def col (j : J) : MatrixL2 I J →L[ℝ] L2 I :=
  restrictCLM (fun i => (i, j)) (fun _ _ h => (Prod.mk.inj h).1)

@[simp] theorem row_apply (i : I) (x : MatrixL2 I J) (j : J) : row i x j = x (i, j) := rfl
@[simp] theorem col_apply (j : J) (x : MatrixL2 I J) (i : I) : col j x i = x (i, j) := rfl

theorem summable_norm_sq_outer (x : L2 I) (y : L2 J) :
    Summable (fun p : I × J => ‖x p.1 * y p.2‖ ^ (2 : ℕ)) := by
  simpa only [norm_mul, mul_pow] using
    (summable_norm_sq x).mul_of_nonneg (summable_norm_sq y)
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)

/-- A pure real Hilbert tensor in coordinate form. -/
def outer (x : L2 I) (y : L2 J) : MatrixL2 I J :=
  ⟨fun p => x p.1 * y p.2, memℓp_gen (by simpa using summable_norm_sq_outer x y)⟩

@[simp] theorem outer_apply (x : L2 I) (y : L2 J) (p : I × J) :
    outer x y p = x p.1 * y p.2 := rfl

theorem norm_outer (x : L2 I) (y : L2 J) : ‖outer x y‖ = ‖x‖ * ‖y‖ := by
  have hsum : Summable (fun p : I × J => ‖x p.1‖ ^ (2 : ℕ) * ‖y p.2‖ ^ (2 : ℕ)) :=
    (summable_norm_sq x).mul_of_nonneg (summable_norm_sq y)
      (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
  have hsq : ‖outer x y‖ ^ (2 : ℕ) = (‖x‖ * ‖y‖) ^ (2 : ℕ) := by
    rw [norm_sq, mul_pow, norm_sq, norm_sq,
      (summable_norm_sq x).tsum_mul_tsum (summable_norm_sq y) hsum]
    simp only [outer_apply, norm_mul, mul_pow]
  nlinarith [norm_nonneg (outer x y), mul_nonneg (norm_nonneg x) (norm_nonneg y)]

@[simp] theorem outer_zero_left (y : L2 J) : outer (0 : L2 I) y = 0 := by
  ext p; change 0 * y p.2 = 0; exact zero_mul _
@[simp] theorem outer_zero_right (x : L2 I) : outer x (0 : L2 J) = 0 := by
  ext p; change x p.1 * 0 = 0; exact mul_zero _
@[simp] theorem outer_add_left (x x' : L2 I) (y : L2 J) :
    outer (x + x') y = outer x y + outer x' y := by
  ext p; change (x p.1 + x' p.1) * y p.2 = x p.1 * y p.2 + x' p.1 * y p.2; ring
@[simp] theorem outer_add_right (x : L2 I) (y y' : L2 J) :
    outer x (y + y') = outer x y + outer x y' := by
  ext p; change x p.1 * (y p.2 + y' p.2) = x p.1 * y p.2 + x p.1 * y' p.2; ring
@[simp] theorem outer_smul_left (c : ℝ) (x : L2 I) (y : L2 J) :
    outer (c • x) y = c • outer x y := by
  ext p; change (c * x p.1) * y p.2 = c * (x p.1 * y p.2); ring
@[simp] theorem outer_smul_right (c : ℝ) (x : L2 I) (y : L2 J) :
    outer x (c • y) = c • outer x y := by
  ext p; change x p.1 * (c * y p.2) = c * (x p.1 * y p.2); ring

def outerBilinear : L2 I →L[ℝ] L2 J →L[ℝ] MatrixL2 I J :=
  ({ toFun := fun x =>
       { toFun := outer x
         map_add' := outer_add_right x
         map_smul' := by intro c y; exact outer_smul_right c x y }
     map_add' := by intro x x'; apply LinearMap.ext; intro y; exact outer_add_left x x' y
     map_smul' := by intro c x; apply LinearMap.ext; intro y; exact outer_smul_left c x y } :
    L2 I →ₗ[ℝ] L2 J →ₗ[ℝ] MatrixL2 I J).mkContinuous₂ 1
      (by intro x y; simpa using (norm_outer x y).le)

@[simp] theorem outerBilinear_apply (x : L2 I) (y : L2 J) : outerBilinear x y = outer x y := rfl

theorem continuous_outer : Continuous (fun p : L2 I × L2 J => outer p.1 p.2) :=
  by simpa only [Function.uncurry_def, outerBilinear_apply] using
    (outerBilinear (I := I) (J := J)).continuous₂

@[simp] theorem row_outer (i : I) (x : L2 I) (y : L2 J) :
    row i (outer x y) = (x i) • y := by ext j; simp

@[simp] theorem col_outer (j : J) (x : L2 I) (y : L2 J) :
    col j (outer x y) = (y j) • x := by ext i; simp [mul_comm]

end L2Coordinates
end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.Admissible -/
section
/-!
# Admissible parameter families

The ambient Hilbert space is explicit in `HilbertFamily`. Normalization embeds
it into the fixed `RealL2`, giving `AdmissibleFamily`. The span in this record
is always the algebraic real span.
-/

noncomputable section

open Set TopologicalSpace Topology

namespace NoUniversalFSigma

universe u v

/-- Enumerate a countable collection of bounded functionals by the naturals;
numbers outside the encoding range denote the zero functional. -/
def enumerateFunctionals {B : Type u} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {I : Type v} [Countable I] (ℓ : I → B →L[ℝ] ℝ) (n : ℕ) : B →L[ℝ] ℝ :=
  letI : Encodable I := Encodable.ofCountable I
  match Encodable.decode (α := I) n with
  | some i => ℓ i
  | none => 0

theorem exists_enumerateFunctionals_eq {B : Type u}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {I : Type v} [Countable I]
    (ℓ : I → B →L[ℝ] ℝ) (i : I) : ∃ n, enumerateFunctionals ℓ n = ℓ i := by
  letI : Encodable I := Encodable.ofCountable I
  exact ⟨Encodable.encode i, by simp only [enumerateFunctionals, Encodable.encodek]⟩

theorem enumerateFunctionals_locallyConstant {B : Type u}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {P : Type} [TopologicalSpace P]
    {I : Type v} [Countable I] (j : P → B) (ℓ : I → B →L[ℝ] ℝ)
    (hℓ : ∀ i, IsLocallyConstant (ℓ i ∘ j)) (n : ℕ) :
    IsLocallyConstant (enumerateFunctionals ℓ n ∘ j) := by
  letI : Encodable I := Encodable.ofCountable I
  unfold enumerateFunctionals
  split
  · exact hℓ _
  · exact IsLocallyConstant.const (X := P) 0

theorem enumerateFunctionals_separates {B : Type u}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {P : Type}
    {I : Type v} [Countable I] (j : P → B) (ℓ : I → B →L[ℝ] ℝ)
    (hℓ : ∀ p q, p ≠ q → ∃ i, ℓ i (j p) ≠ ℓ i (j q)) :
    ∀ p q, p ≠ q → ∃ n, enumerateFunctionals ℓ n (j p) ≠ enumerateFunctionals ℓ n (j q) := by
  intro p q hpq
  obtain ⟨i, hi⟩ := hℓ p q hpq
  obtain ⟨n, hn⟩ := exists_enumerateFunctionals_eq ℓ i
  exact ⟨n, by simpa only [hn] using hi⟩

/-- The data and proved properties needed for the transfinite family
construction, before the ambient space is normalized. -/
structure HilbertFamily (B : Type u)
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] where
  Parameter : Type
  [topology : TopologicalSpace Parameter]
  [polish : PolishSpace Parameter]
  [nonempty : Nonempty Parameter]
  j : Parameter → B
  bound : ℝ
  norm_j_le : ∀ p, ‖j p‖ ≤ bound
  continuous_j : Continuous j
  closedEmbedding_j : IsClosedEmbedding j
  mass : B →L[ℝ] ℝ
  mass_j : ∀ p, mass (j p) = 1
  separator : ℕ → B →L[ℝ] ℝ
  locallyConstant_separator : ∀ n, IsLocallyConstant (separator n ∘ j)
  separates : ∀ p q, p ≠ q → ∃ n, separator n (j p) ≠ separator n (j q)
  isFSigma_span : IsFSigma (Submodule.span ℝ (range j) : Set B)

attribute [instance] HilbertFamily.topology HilbertFamily.polish HilbertFamily.nonempty

/-- An admissible family in the one fixed real Hilbert space of the main theorem. -/
abbrev AdmissibleFamily := HilbertFamily RealL2

namespace HilbertFamily

variable {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- The algebraic span of a family. -/
abbrev span (A : HilbertFamily B) : Submodule ℝ B := Submodule.span ℝ (range A.j)

theorem j_mem_span (A : HilbertFamily B) (p : A.Parameter) : A.j p ∈ A.span :=
  Submodule.subset_span (mem_range_self p)

/-- The source diagonal survival property at a specified small ordinal. -/
def HasDiagonalRank (A : HilbertFamily B) (α : Ordinal.{0}) : Prop :=
  ∀ p, (p, p) ∈ escapeRemainder (A.span : Set B) A.j α

/-- The generic constructor accepts any countable separator index. -/
def ofCountableSeparators
    {P : Type} [TopologicalSpace P] [PolishSpace P] [Nonempty P]
    (j : P → B) (bound : ℝ) (hnorm : ∀ p, ‖j p‖ ≤ bound)
    (hj : Continuous j) (hclosed : IsClosedEmbedding j)
    (mass : B →L[ℝ] ℝ) (hmass : ∀ p, mass (j p) = 1)
    {I : Type v} [Countable I] (ℓ : I → B →L[ℝ] ℝ)
    (hlc : ∀ i, IsLocallyConstant (ℓ i ∘ j))
    (hsep : ∀ p q, p ≠ q → ∃ i, ℓ i (j p) ≠ ℓ i (j q))
    (hspan : IsFSigma (Submodule.span ℝ (range j) : Set B)) : HilbertFamily B where
  Parameter := P
  j := j
  bound := bound
  norm_j_le := hnorm
  continuous_j := hj
  closedEmbedding_j := hclosed
  mass := mass
  mass_j := hmass
  separator := enumerateFunctionals ℓ
  locallyConstant_separator := enumerateFunctionals_locallyConstant j ℓ hlc
  separates := enumerateFunctionals_separates j ℓ hsep
  isFSigma_span := hspan

end HilbertFamily

export HilbertFamily (HasDiagonalRank)

/-- Normalize an actual separable complete Hilbert family into `RealL2`.
Mass and separators are extended by the adjoint of the isometric embedding. -/
def normalizeFamily {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] [SeparableSpace B] (A : HilbertFamily B) : AdmissibleFamily where
  Parameter := A.Parameter
  j := fun p => hilbertEmbedding B (A.j p)
  bound := A.bound
  norm_j_le p := by simpa only [LinearIsometry.norm_map] using A.norm_j_le p
  continuous_j := (hilbertEmbedding B).continuous.comp A.continuous_j
  closedEmbedding_j := isClosedEmbedding_comp_linearIsometry (hilbertEmbedding B) A.closedEmbedding_j
  mass := extendFunctional (hilbertEmbedding B) A.mass
  mass_j p := by simp only [extendFunctional_apply_embedding, A.mass_j]
  separator n := extendFunctional (hilbertEmbedding B) (A.separator n)
  locallyConstant_separator n := by
    simpa only [Function.comp_def, extendFunctional_apply_embedding] using A.locallyConstant_separator n
  separates p q hpq := by
    obtain ⟨n, hn⟩ := A.separates p q hpq
    exact ⟨n, by simpa only [extendFunctional_apply_embedding] using hn⟩
  isFSigma_span := by
    rw [span_range_comp_linearIsometry]
    exact isFSigma_map_submodule (hilbertEmbedding B) A.span A.isFSigma_span

theorem normalizeFamily_hasDiagonalRank
    {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [CompleteSpace B] [SeparableSpace B] (A : HilbertFamily B)
    (α : Ordinal.{0}) (hα : HasDiagonalRank A α) : HasDiagonalRank (normalizeFamily A) α := by
  have hspan : ((normalizeFamily A).span : Set RealL2) =
      hilbertEmbedding B '' (A.span : Set B) := by
    change (Submodule.span ℝ (range (fun p => hilbertEmbedding B (A.j p))) : Set RealL2) = _
    rw [span_range_comp_linearIsometry]
    rfl
  intro p
  rw [hspan]
  exact escapeRemainder_image_linearIsometry (hilbertEmbedding B) (A.span : Set B) A.j α (hα p)

/-- The explicit branch construction of Section 5, with all admissibility
properties already proved in the branch modules. -/
def branchHilbertFamily : HilbertFamily Branch.Hilbert where
  Parameter := Branch.Parameter
  j := Branch.family
  bound := 8 / 3
  norm_j_le := Branch.norm_family_le
  continuous_j := Branch.continuous_family
  closedEmbedding_j := Branch.isClosedEmbedding_family
  mass := Branch.mass
  mass_j := Branch.mass_family
  separator := Branch.separatingFunctionals
  locallyConstant_separator := Branch.separatingFunctionals_locallyConstant
  separates _ _ h := Branch.separatingFunctionals_separate h
  isFSigma_span := Branch.isFSigma_span

/-- The actual base admissible family in the fixed standard Hilbert space. -/
def baseFamily : AdmissibleFamily := normalizeFamily branchHilbertFamily

theorem baseFamily_hasDiagonalRank_one : HasDiagonalRank baseFamily 1 :=
  normalizeFamily_hasDiagonalRank branchHilbertFamily 1 Branch.diagonal_rank_one

theorem HilbertFamily.hasDiagonalRank_zero
    {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    (A : HilbertFamily B) : HasDiagonalRank A 0 := by
  intro p
  rw [escapeRemainder_zero]
  exact mem_univ _

/-- The genuine Hilbert product of two admissible families, before ambient
normalization. Separators in the two factors are enumerated together. -/
def hilbertProductFamilyData
    {B : Type u} {D : Type v}
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    (A : HilbertFamily B) (K : HilbertFamily D) :
    HilbertFamily (WithLp 2 (B × D)) :=
  HilbertFamily.ofCountableSeparators (hilbertProductFamily A.j K.j)
    (‖(WithLp.prodContinuousLinearEquiv 2 ℝ B D).symm.toContinuousLinearMap‖ * max A.bound K.bound)
    (norm_hilbertProductFamily_le A.j K.j A.norm_j_le K.norm_j_le)
    (continuous_hilbertProductFamily A.continuous_j K.continuous_j)
    (isClosedEmbedding_hilbertProductFamily A.closedEmbedding_j K.closedEmbedding_j)
    (hilbertProductMass A.mass) (hilbertProductMass_family A.j K.j A.mass A.mass_j)
    (hilbertProductSeparator A.separator K.separator)
    (hilbertProductSeparator_locallyConstant A.j K.j A.separator K.separator
      A.locallyConstant_separator K.locallyConstant_separator)
    (hilbertProductSeparator_separates A.j K.j A.separator K.separator A.separates K.separates)
    (isFSigma_span_hilbertProductFamily A.j K.j A.mass K.mass
      A.mass_j K.mass_j A.isFSigma_span K.isFSigma_span)

theorem hilbertProductFamilyData_hasDiagonalRank_succ
    {B : Type u} {D : Type v}
    [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D]
    (A : HilbertFamily B) (K : HilbertFamily D) (α : Ordinal.{0})
    (hA : HasDiagonalRank A α) (hK : HasDiagonalRank K 1) :
    HasDiagonalRank (hilbertProductFamilyData A K) (α + 1) :=
  diagonal_escape_hilbertProduct_succ A.j K.j α hA hK

/-- The actual successor admissible family, normalized back into `RealL2`. -/
def successorFamily (A : AdmissibleFamily) : AdmissibleFamily :=
  normalizeFamily (hilbertProductFamilyData A baseFamily)

theorem successorFamily_hasDiagonalRank (A : AdmissibleFamily) (α : Ordinal.{0})
    (hA : HasDiagonalRank A α) : HasDiagonalRank (successorFamily A) (α + 1) :=
  normalizeFamily_hasDiagonalRank (hilbertProductFamilyData A baseFamily) (α + 1)
    (hilbertProductFamilyData_hasDiagonalRank_succ A baseFamily α hA baseFamily_hasDiagonalRank_one)

/-- Concrete admissible witnesses at every finite ordinal. -/
def finiteRankFamily : ℕ → AdmissibleFamily
  | 0 => baseFamily
  | n + 1 => successorFamily (finiteRankFamily n)

theorem finiteRankFamily_hasDiagonalRank (n : ℕ) :
    HasDiagonalRank (finiteRankFamily n) (n : Ordinal.{0}) := by
  induction n with
  | zero => exact HilbertFamily.hasDiagonalRank_zero _
  | succ n ih =>
    exact successorFamily_hasDiagonalRank (finiteRankFamily n) n ih

end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.FiniteL2 -/
section
noncomputable section
open scoped BigOperators ENNReal
open Set Topology

namespace NoUniversalFSigma
namespace FiniteL2

open L2Coordinates
universe u v

/-- Reindexing is a real linear isometric equivalence of coordinate Hilbert spaces. -/
def reindex {I : Type u} {J : Type v} (e : I ≃ J) : L2 I ≃ₗᵢ[ℝ] L2 J where
  toFun := restrict e.symm e.symm.injective
  invFun := restrict e e.injective
  left_inv x := by ext i; simp
  right_inv x := by ext j; simp
  map_add' x y := by ext j; rfl
  map_smul' a x := by ext j; rfl
  norm_map' x := by
    apply le_antisymm (norm_restrict_le _ _ _)
    have h := norm_restrict_le e e.injective (restrict e.symm e.symm.injective x)
    have he : restrict e e.injective (restrict e.symm e.symm.injective x) = x := by ext i; simp
    rwa [he] at h

@[simp] theorem reindex_apply {I : Type u} {J : Type v} (e : I ≃ J) (x : L2 I) (j : J) :
    reindex e x j = x (e.symm j) := rfl

/-- Finite tensor atoms, recursively assembled using the actual Hilbert outer product. -/
def pureFin {J : Type v} : (n : ℕ) → (Fin n → L2 J) → L2 (Fin n → J)
  | 0, _ => lp.single 2 (fun i : Fin 0 => Fin.elim0 i) (1 : ℝ)
  | n + 1, v => reindex (Fin.consEquiv (fun _ : Fin (n + 1) => J))
      (outer (v 0) (pureFin n (fun i => v i.succ)))

theorem pureFin_apply {J : Type v} (n : ℕ) (v : Fin n → L2 J) (a : Fin n → J) :
    pureFin n v a = ∏ i, v i (a i) := by
  induction n with
  | zero =>
    have he : a = (fun i : Fin 0 => Fin.elim0 i) := Subsingleton.elim _ _
    simp only [Fin.prod_univ_zero]
    change (Pi.single (fun i : Fin 0 => Fin.elim0 i) (1 : ℝ) : (Fin 0 → J) → ℝ) a = 1
    rw [he]
    exact Pi.single_eq_same _ _
  | succ n ih =>
    simp [pureFin, reindex_apply, Fin.consEquiv, outer_apply, ih, Fin.prod_univ_succ, Fin.tail]

theorem norm_pureFin {J : Type v} (n : ℕ) (v : Fin n → L2 J) : ‖pureFin n v‖ = ∏ i, ‖v i‖ := by
  induction n with
  | zero => simp [pureFin, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  | succ n ih =>
    rw [pureFin, LinearIsometryEquiv.norm_map, norm_outer, ih, Fin.prod_univ_succ]

theorem continuous_pureFin {J : Type v} (n : ℕ) : Continuous (pureFin (J := J) n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    have ht : Continuous (fun v : Fin (n + 1) → L2 J => pureFin n (fun i => v i.succ)) :=
      ih.comp (continuous_pi (fun i => continuous_apply i.succ))
    exact (reindex (Fin.consEquiv (fun _ : Fin (n + 1) => J))).continuous.comp
      (continuous_outer.comp ((continuous_apply 0).prodMk ht))

/-- The finite Hilbert tensor atom for an arbitrary finite index type. -/
def pure {I : Type u} {J : Type v} [Fintype I] (v : I → L2 J) : L2 (I → J) :=
  reindex (Equiv.arrowCongr (Fintype.equivFin I).symm (Equiv.refl J))
    (pureFin (Fintype.card I) (fun i => v ((Fintype.equivFin I).symm i)))

theorem pure_apply {I : Type u} {J : Type v} [Fintype I] (v : I → L2 J) (a : I → J) :
    pure v a = ∏ i, v i (a i) := by
  rw [pure, reindex_apply, pureFin_apply]
  exact Fintype.prod_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

theorem norm_pure {I : Type u} {J : Type v} [Fintype I] (v : I → L2 J) :
    ‖pure v‖ = ∏ i, ‖v i‖ := by
  rw [pure, LinearIsometryEquiv.norm_map, norm_pureFin]
  exact Fintype.prod_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

theorem continuous_pure {I : Type u} {J : Type v} [Fintype I] :
    Continuous (pure (I := I) (J := J)) := by
  exact (reindex (Equiv.arrowCongr (Fintype.equivFin I).symm (Equiv.refl J))).continuous.comp
    ((continuous_pureFin _).comp (continuous_pi (fun i => continuous_apply _)))

/-- The packet indexed by all natural-valued coordinate assignments on a finite set. -/
abbrev Packet (F : Finset ℕ) := L2 (F → ℕ)

def atom (F : Finset ℕ) (v : ℕ → RealL2) : Packet F := pure (fun i : F => v i)

@[simp] theorem atom_apply (F : Finset ℕ) (v : ℕ → RealL2) (a : F → ℕ) :
    atom F v a = ∏ n : F, v n (a n) := pure_apply _ _

@[simp] theorem norm_atom (F : Finset ℕ) (v : ℕ → RealL2) :
    ‖atom F v‖ = ∏ n : F, ‖v n‖ := norm_pure _

theorem continuous_atom (F : Finset ℕ) : Continuous (atom F) :=
  continuous_pure.comp (continuous_pi (fun i => continuous_apply (i : ℕ)))

/-- Splitting a finite packet along two disjoint coordinate blocks. -/
def packetUnion (F W : Finset ℕ) (h : Disjoint F W) :
    Packet (F ∪ W) ≃ₗᵢ[ℝ] MatrixL2 (F → ℕ) (W → ℕ) :=
  reindex (Equiv.piFinsetUnion (fun _ : ℕ => ℕ) h).symm

@[simp] theorem packetUnion_apply (F W : Finset ℕ) (h : Disjoint F W)
    (x : Packet (F ∪ W)) (a : F → ℕ) (b : W → ℕ) :
    packetUnion F W h x (a, b) = x (Equiv.piFinsetUnion (fun _ : ℕ => ℕ) h (a, b)) := rfl

theorem packetUnion_atom (F W : Finset ℕ) (h : Disjoint F W) (v : ℕ → RealL2) :
    packetUnion F W h (atom (F ∪ W) v) = outer (atom F v) (atom W v) := by
  ext p
  rw [packetUnion_apply, outer_apply, atom_apply, atom_apply, atom_apply]
  let e := Equiv.Finset.union F W h
  let a := Equiv.piFinsetUnion (fun _ : ℕ => ℕ) h p
  change (∏ n : (F ∪ W : Finset ℕ), v n (a n)) =
    (∏ n : F, v n (p.1 n)) * (∏ n : W, v n (p.2 n))
  calc
    _ = ∏ n : F ⊕ W, v (e n) (a (e n)) :=
      (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      congr 1
      · apply Finset.prod_congr rfl
        intro n _
        simp only [e, Equiv.Finset.union_inl, a]
        rw [Equiv.piFinsetUnion_left (fun _ : ℕ => ℕ) h n.property _]
      · apply Finset.prod_congr rfl
        intro n _
        simp only [e, Equiv.Finset.union_inr, a]
        rw [Equiv.piFinsetUnion_right (fun _ : ℕ => ℕ) h n.property _]

def singletonIndex (n : ℕ) : (({n} : Finset ℕ) → ℕ) ≃ ℕ where
  toFun a := a ⟨n, Finset.mem_singleton_self n⟩
  invFun k := fun _ => k
  left_inv a := by
    funext i
    have hi : i = ⟨n, Finset.mem_singleton_self n⟩ := Subtype.ext (Finset.mem_singleton.1 i.property)
    simp only [hi]
  right_inv _ := rfl

def packetSingleton (n : ℕ) : Packet {n} ≃ₗᵢ[ℝ] RealL2 := reindex (singletonIndex n)

@[simp] theorem packetSingleton_atom (n : ℕ) (v : ℕ → RealL2) :
    packetSingleton n (atom {n} v) = v n := by
  ext k
  change pure (fun i : ({n} : Finset ℕ) => v i) (fun _ => k) = v n k
  rw [pure_apply]
  exact (Finset.prod_coe_sort ({n} : Finset ℕ) (fun m => v m k)).trans (by simp)

theorem atom_smul (F : Finset ℕ) (b : ℕ → ℝ) (v : ℕ → RealL2) :
    atom F (fun n => b n • v n) = (∏ n : F, b n) • atom F v := by
  ext a
  change atom F (fun n => b n • v n) a = (∏ n : F, b n) * atom F v a
  simp only [atom_apply]
  change (∏ n : F, b n * v n (a n)) = (∏ n : F, b n) * ∏ n : F, v n (a n)
  exact Finset.prod_mul_distrib

/-- The one-factor Hilbert augmentation, with the mass coordinate at `none`. -/
def augment (a : ℝ) (v : RealL2) : L2 (Option ℕ) := by
  let f : ℕ ⊕ Unit → ℝ := Sum.elim (fun n => ‖v n‖ ^ (2 : ℕ)) (fun _ => ‖a‖ ^ (2 : ℕ))
  have hs : Summable f := Summable.sum f (summable_norm_sq v) ((hasSum_fintype _).summable)
  let he : Option ℕ ≃ ℕ ⊕ Unit := Equiv.optionEquivSumPUnit ℕ
  have hc := hs.comp_injective he.injective
  refine ⟨(fun o : Option ℕ => o.elim a (fun n => v n)), memℓp_gen ?_⟩
  have hnorm : Summable (fun o : Option ℕ => ‖o.elim a (fun n => v n)‖ ^ (2 : ℕ)) := by
    convert hc using 1
    funext o
    cases o <;> rfl
  simpa using hnorm

@[simp] theorem augment_none (a : ℝ) (v : RealL2) : augment a v none = a := rfl
@[simp] theorem augment_some (a : ℝ) (v : RealL2) (n : ℕ) : augment a v (some n) = v n := rfl

theorem norm_augment_sq (a : ℝ) (v : RealL2) : ‖augment a v‖ ^ (2 : ℕ) = ‖a‖ ^ (2 : ℕ) + ‖v‖ ^ (2 : ℕ) := by
  rw [norm_sq]
  let e : Option ℕ ≃ ℕ ⊕ Unit := Equiv.optionEquivSumPUnit ℕ
  rw [← e.symm.tsum_eq (fun o => ‖augment a v o‖ ^ (2 : ℕ))]
  rw [Summable.tsum_sum (by simpa [e] using summable_norm_sq v)
    ((hasSum_fintype _).summable)]
  simp only [e, Equiv.optionEquivSumPUnit_symm_inl, augment_some,
    Equiv.optionEquivSumPUnit_symm_inr, augment_none, tsum_fintype,
    Fintype.sum_unique, ← norm_sq]
  ring

def head : L2 (Option ℕ) →L[ℝ] ℝ := lp.evalCLM ℝ _ 2 none
def tail : L2 (Option ℕ) →L[ℝ] RealL2 := restrictCLM some (Option.some_injective ℕ)

@[simp] theorem head_augment (a : ℝ) (v : RealL2) : head (augment a v) = a := rfl
@[simp] theorem tail_augment (a : ℝ) (v : RealL2) : tail (augment a v) = v := by ext n; rfl

@[simp] theorem augment_head_tail (v : L2 (Option ℕ)) : augment (head v) (tail v) = v := by
  ext o
  cases o <;> rfl

theorem norm_augment_le (a : ℝ) (v : RealL2) : ‖augment a v‖ ≤ 2 * ‖(a, v)‖ := by
  have hs := norm_augment_sq a v
  have ha : ‖a‖ ≤ ‖(a, v)‖ := le_max_left _ _
  have hv : ‖v‖ ≤ ‖(a, v)‖ := le_max_right _ _
  nlinarith [norm_nonneg (augment a v), norm_nonneg (a, v), norm_nonneg a, norm_nonneg v]

def augmentCLM : (ℝ × RealL2) →L[ℝ] L2 (Option ℕ) :=
  ({ toFun := fun p => augment p.1 p.2
     map_add' := by intro p q; ext o; cases o <;> rfl
     map_smul' := by intro a p; ext o; cases o <;> rfl } :
    (ℝ × RealL2) →ₗ[ℝ] L2 (Option ℕ)).mkContinuous 2
      (fun p => norm_augment_le p.1 p.2)

@[simp] theorem augmentCLM_apply (a : ℝ) (v : RealL2) : augmentCLM (a, v) = augment a v := rfl

theorem augment_injective : Function.Injective (fun p : ℝ × RealL2 => augment p.1 p.2) := by
  intro p q h
  exact Prod.ext (by simpa only [head_augment] using congrArg head h)
    (by simpa only [tail_augment] using congrArg tail h)

/-- The finite augmented packet contains all subset-coordinate components. -/
abbrev AugmentedPacket (F : Finset ℕ) := L2 (F → Option ℕ)

def augmentedAtom (F : Finset ℕ) (v : ℕ → RealL2) : AugmentedPacket F :=
  pure (fun n : F => augment 1 (v n))

@[simp] theorem augmentedAtom_apply (F : Finset ℕ) (v : ℕ → RealL2) (a : F → Option ℕ) :
    augmentedAtom F v a = ∏ n : F, (a n).elim 1 (fun k => v n k) := pure_apply _ _

theorem continuous_augmentedAtom (F : Finset ℕ) : Continuous (augmentedAtom F) :=
  continuous_pure.comp (continuous_pi (fun n =>
    augmentCLM.continuous.comp (continuous_const.prodMk (continuous_apply (n : ℕ)))))

def pureUnion {J : Type v} (F W : Finset ℕ) (h : Disjoint F W) :
    L2 ((F ∪ W : Finset ℕ) → J) ≃ₗᵢ[ℝ] MatrixL2 (F → J) (W → J) :=
  reindex (Equiv.piFinsetUnion (fun _ : ℕ => J) h).symm

theorem pureUnion_pure {J : Type v} (F W : Finset ℕ) (h : Disjoint F W) (v : ℕ → L2 J) :
    pureUnion F W h (pure (fun n : (F ∪ W : Finset ℕ) => v n)) =
      outer (pure (fun n : F => v n)) (pure (fun n : W => v n)) := by
  ext p
  change pure (fun n : (F ∪ W : Finset ℕ) => v n)
      (Equiv.piFinsetUnion (fun _ : ℕ => J) h p) = _
  rw [outer_apply, pure_apply, pure_apply, pure_apply]
  let e := Equiv.Finset.union F W h
  let a := Equiv.piFinsetUnion (fun _ : ℕ => J) h p
  change (∏ n : (F ∪ W : Finset ℕ), v n (a n)) =
    (∏ n : F, v n (p.1 n)) * (∏ n : W, v n (p.2 n))
  calc
    _ = ∏ n : F ⊕ W, v (e n) (a (e n)) :=
      (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      congr 1
      · apply Finset.prod_congr rfl
        intro n _
        simp only [e, Equiv.Finset.union_inl, a]
        rw [Equiv.piFinsetUnion_left (fun _ : ℕ => J) h n.property _]
      · apply Finset.prod_congr rfl
        intro n _
        simp only [e, Equiv.Finset.union_inr, a]
        rw [Equiv.piFinsetUnion_right (fun _ : ℕ => J) h n.property _]

def augmentedPacketUnion (F W : Finset ℕ) (h : Disjoint F W) :
    AugmentedPacket (F ∪ W) ≃ₗᵢ[ℝ] MatrixL2 (F → Option ℕ) (W → Option ℕ) := pureUnion F W h

theorem augmentedPacketUnion_atom (F W : Finset ℕ) (h : Disjoint F W) (v : ℕ → RealL2) :
    augmentedPacketUnion F W h (augmentedAtom (F ∪ W) v) =
      outer (augmentedAtom F v) (augmentedAtom W v) :=
  pureUnion_pure F W h (fun n => augment 1 (v n))

end FiniteL2
end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.L2Injection -/
section
noncomputable section

open Set
open scoped RealInnerProductSpace
attribute [local instance] Classical.decEq

namespace NoUniversalFSigma.L2Coordinates

universe u v
variable {I : Type u} {J : Type v}

/-- Zero extension along an injective coordinate map, defined as the adjoint
of coordinate restriction. -/
def extendCLM (e : I → J) (he : Function.Injective e) : L2 I →L[ℝ] L2 J :=
  (restrictCLM e he).adjoint

theorem restrict_single (e : I → J) (he : Function.Injective e) (i : I) (a : ℝ) :
    restrictCLM e he (lp.single 2 (e i) a) = lp.single 2 i a := by
  classical
  ext k
  simp only [restrictCLM_apply, lp.coeFn_single]
  by_cases h : k = i
  · subst k; simp
  · have hek : e k ≠ e i := fun hki => h (he hki)
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne hek]

@[simp] theorem extendCLM_apply_image (e : I → J) (he : Function.Injective e)
    (x : L2 I) (i : I) : extendCLM e he x (e i) = x i := by
  classical
  have h := (restrictCLM e he).adjoint_inner_left (lp.single 2 (e i) (1 : ℝ)) x
  simpa [extendCLM, restrict_single, lp.inner_single_right] using h

theorem extendCLM_apply_of_not_mem_range (e : I → J) (he : Function.Injective e)
    (x : L2 I) (j : J) (hj : j ∉ range e) : extendCLM e he x j = 0 := by
  classical
  have hz : restrictCLM e he (lp.single 2 j (1 : ℝ)) = 0 := by
    ext i
    have hne : e i ≠ j := fun h => hj ⟨i, h⟩
    change (Pi.single j (1 : ℝ) : J → ℝ) (e i) = (0 : ℝ)
    simp only [Pi.single_eq_of_ne hne]
  have h := (restrictCLM e he).adjoint_inner_left (lp.single 2 j (1 : ℝ)) x
  simpa [extendCLM, hz, lp.inner_single_right] using h

@[simp] theorem restrict_extendCLM (e : I → J) (he : Function.Injective e) (x : L2 I) :
    restrictCLM e he (extendCLM e he x) = x := by
  ext i
  exact extendCLM_apply_image e he x i

theorem norm_restrictCLM_le (e : I → J) (he : Function.Injective e) :
    ‖restrictCLM e he‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (by
    intro x
    simpa using norm_restrict_le e he x)

theorem norm_extendCLM (e : I → J) (he : Function.Injective e) (x : L2 I) :
    ‖extendCLM e he x‖ = ‖x‖ := by
  apply le_antisymm
  · calc
      ‖extendCLM e he x‖ ≤ ‖extendCLM e he‖ * ‖x‖ :=
        (extendCLM e he).le_opNorm x
      _ ≤ 1 * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
        simpa only [extendCLM, ContinuousLinearMap.adjoint.norm_map] using
          norm_restrictCLM_le e he
      _ = ‖x‖ := one_mul _
  · have h := norm_restrict_le e he (extendCLM e he x)
    change ‖restrictCLM e he (extendCLM e he x)‖ ≤ _ at h
    simpa only [restrict_extendCLM] using h

/-- Isometric insertion into a family of coordinates. -/
def extend (e : I → J) (he : Function.Injective e) : L2 I →ₗᵢ[ℝ] L2 J :=
  { (extendCLM e he).toLinearMap with norm_map' := norm_extendCLM e he }

@[simp] theorem extend_apply_image (e : I → J) (he : Function.Injective e)
    (x : L2 I) (i : I) : extend e he x (e i) = x i :=
  extendCLM_apply_image e he x i

theorem extend_apply_of_not_mem_range (e : I → J) (he : Function.Injective e)
    (x : L2 I) (j : J) (hj : j ∉ range e) : extend e he x j = 0 :=
  extendCLM_apply_of_not_mem_range e he x j hj

end NoUniversalFSigma.L2Coordinates
end
end

/- Source module: NoUniversalFSigma.TensorFamily -/
section
/-! The countable square-free finite tensor family. All components live in
one countably indexed real Hilbert space. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2

abbrev Index := Σ F : Finset ℕ, (F → ℕ)
abbrev Fock := L2 Index
abbrev Parameter (A : ℕ → AdmissibleFamily) := ∀ n, (A n).Parameter

def blockIndex (F : Finset ℕ) : (F → ℕ) → Index := fun a => ⟨F, a⟩
theorem blockIndex_injective (F : Finset ℕ) : Function.Injective (blockIndex F) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

def insertBlock (F : Finset ℕ) : Packet F →ₗᵢ[ℝ] Fock :=
  extend (blockIndex F) (blockIndex_injective F)
def block (F : Finset ℕ) : Fock →L[ℝ] Packet F :=
  restrictCLM (blockIndex F) (blockIndex_injective F)

@[simp] theorem block_apply (F : Finset ℕ) (x : Fock) (a : F → ℕ) :
    block F x a = x ⟨F, a⟩ := rfl

@[simp] theorem block_insertBlock (F : Finset ℕ) (x : Packet F) :
    block F (insertBlock F x) = x := by
  ext a
  exact extend_apply_image _ _ _ _

theorem block_insertBlock_ne (F G : Finset ℕ) (h : F ≠ G) (x : Packet G) :
    block F (insertBlock G x) = 0 := by
  ext a
  change extend (blockIndex G) (blockIndex_injective G) x ⟨F, a⟩ = (0 : ℝ)
  apply extend_apply_of_not_mem_range
  rintro ⟨b, hb⟩
  exact h (congrArg Sigma.fst hb).symm

def decay (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 1)
theorem decay_pos (n : ℕ) : 0 < decay n := by unfold decay; positivity
theorem summable_decay : Summable decay := by
  simpa only [decay] using
    (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1))

def weight (A : ℕ → AdmissibleFamily) (n : ℕ) : ℝ :=
  decay n / (1 + max 0 (A n).bound)
theorem weight_pos (A : ℕ → AdmissibleFamily) (n : ℕ) : 0 < weight A n := by
  exact div_pos (decay_pos n) (by positivity)
theorem weight_ne_zero (A : ℕ → AdmissibleFamily) (n : ℕ) : weight A n ≠ 0 :=
  ne_of_gt (weight_pos A n)

theorem norm_weight_smul_le (A : ℕ → AdmissibleFamily) (q : Parameter A) (n : ℕ) :
    ‖weight A n • (A n).j (q n)‖ ≤ decay n := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos A n)]
  apply (mul_le_mul_of_nonneg_left ((A n).norm_j_le (q n)) (le_of_lt (weight_pos A n))).trans
  unfold weight
  have hb : (A n).bound ≤ 1 + max 0 (A n).bound :=
    le_trans (le_max_right _ _) (by linarith [le_max_left (0 : ℝ) (A n).bound])
  have hd : 0 < 1 + max 0 (A n).bound := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  exact mul_le_mul_of_nonneg_left hb (decay_pos n).le

def envelope (F : Finset ℕ) : ℝ := ∏ n ∈ F, decay n
theorem envelope_nonneg (F : Finset ℕ) : 0 ≤ envelope F :=
  Finset.prod_nonneg (fun n _ => (decay_pos n).le)
theorem summable_envelope : Summable envelope :=
  summable_finsetProd_of_summable_nonneg (fun n => (decay_pos n).le) summable_decay

def component (A : ℕ → AdmissibleFamily) (q : Parameter A) (F : Finset ℕ) : Packet F :=
  atom F (fun n => weight A n • (A n).j (q n))

theorem norm_component_le (A : ℕ → AdmissibleFamily) (q : Parameter A) (F : Finset ℕ) :
    ‖component A q F‖ ≤ envelope F := by
  rw [component, norm_atom]
  unfold envelope
  rw [← Finset.prod_coe_sort F (fun n => decay n)]
  exact Finset.prod_le_prod (fun n _ => norm_nonneg _) (fun n _ => norm_weight_smul_le A q n)

theorem continuous_component (A : ℕ → AdmissibleFamily) (F : Finset ℕ) :
    Continuous (fun q : Parameter A => component A q F) :=
  (continuous_atom F).comp (continuous_pi (fun n =>
    ((A n).continuous_j.comp (continuous_apply n)).const_smul (weight A n)))

def term (A : ℕ → AdmissibleFamily) (F : Finset ℕ) (q : Parameter A) : Fock :=
  insertBlock F (component A q F)

theorem norm_term_le (A : ℕ → AdmissibleFamily) (F : Finset ℕ) (q : Parameter A) :
    ‖term A F q‖ ≤ envelope F := by
  simpa only [term, LinearIsometry.norm_map] using norm_component_le A q F

theorem summable_norm_term (A : ℕ → AdmissibleFamily) (q : Parameter A) :
    Summable (fun F => ‖term A F q‖) :=
  summable_envelope.of_nonneg_of_le (fun _ => norm_nonneg _) (fun F => norm_term_le A F q)

theorem summable_term (A : ℕ → AdmissibleFamily) (q : Parameter A) :
    Summable (fun F => term A F q) := (summable_norm_term A q).of_norm

def family (A : ℕ → AdmissibleFamily) (q : Parameter A) : Fock := ∑' F, term A F q

theorem continuous_family (A : ℕ → AdmissibleFamily) : Continuous (family A) := by
  exact continuous_tsum (fun F => (insertBlock F).continuous.comp (continuous_component A F))
    summable_envelope (norm_term_le A)

theorem norm_family_le (A : ℕ → AdmissibleFamily) (q : Parameter A) :
    ‖family A q‖ ≤ ∑' F, envelope F :=
  (norm_tsum_le_tsum_norm (summable_norm_term A q)).trans
    ((summable_norm_term A q).tsum_le_tsum (norm_term_le A · q) summable_envelope)

@[simp] theorem block_family (A : ℕ → AdmissibleFamily) (q : Parameter A) (F : Finset ℕ) :
    block F (family A q) = component A q F := by
  rw [family, (block F).map_tsum (summable_term A q)]
  rw [tsum_eq_single F]
  · exact block_insertBlock F _
  · intro G hG
    exact block_insertBlock_ne F G (Ne.symm hG) _

@[simp] theorem family_apply (A : ℕ → AdmissibleFamily) (q : Parameter A)
    (F : Finset ℕ) (a : F → ℕ) :
    family A q ⟨F, a⟩ = ∏ n : F, weight A n * (A n).j (q n) (a n) := by
  have h := congrArg (fun x : Packet F => x a) (block_family A q F)
  simpa only [block_apply, component, atom_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul] using h

def singleton (n : ℕ) : Fock →L[ℝ] RealL2 :=
  (packetSingleton n).toContinuousLinearEquiv.toContinuousLinearMap.comp (block {n})

@[simp] theorem singleton_family (A : ℕ → AdmissibleFamily) (q : Parameter A) (n : ℕ) :
    singleton n (family A q) = weight A n • (A n).j (q n) := by
  change packetSingleton n (block {n} (family A q)) = _
  rw [block_family]
  exact packetSingleton_atom n _

def mass : Fock →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : Index => ℝ) 2
  ⟨(∅ : Finset ℕ), fun i : (∅ : Finset ℕ) => False.elim (Finset.notMem_empty i.val i.property)⟩

@[simp] theorem mass_family (A : ℕ → AdmissibleFamily) (q : Parameter A) :
    mass (family A q) = 1 := by
  change family A q ⟨∅, _⟩ = 1
  rw [family_apply]
  simp

/-- Normalized singleton recovery of the original Hilbert coordinate. -/
def recover (A : ℕ → AdmissibleFamily) (n : ℕ) : Fock →L[ℝ] RealL2 :=
  (weight A n)⁻¹ • singleton n

@[simp] theorem recover_family (A : ℕ → AdmissibleFamily) (q : Parameter A) (n : ℕ) :
    recover A n (family A q) = (A n).j (q n) := by
  simp [recover, smul_smul, inv_mul_cancel₀ (weight_ne_zero A n)]

theorem isEmbedding_family (A : ℕ → AdmissibleFamily) : IsEmbedding (family A) := by
  have hrec : Continuous (fun x : Fock => fun n => recover A n x) :=
    continuous_pi (fun n => (recover A n).continuous)
  apply IsEmbedding.of_comp (continuous_family A) hrec
  simpa only [Function.comp_def, recover_family] using
    (IsEmbedding.piMap (fun n => (A n).closedEmbedding_j.isEmbedding))

theorem isClosed_range_family (A : ℕ → AdmissibleFamily) : IsClosed (range (family A)) := by
  apply IsSeqClosed.isClosed
  intro y z hy hz
  choose q hq using hy
  have hcoord (n : ℕ) :
      Tendsto (fun l => (A n).j (q l n)) atTop (𝓝 (recover A n z)) := by
    have h := ((recover A n).continuous.tendsto z).comp hz
    have heq (l : ℕ) : recover A n (y l) = (A n).j (q l n) := by
      rw [← hq l, recover_family]
    simpa only [Function.comp_def, heq] using h
  have hex (n : ℕ) : ∃ p : (A n).Parameter, (A n).j p = recover A n z :=
    (A n).closedEmbedding_j.isClosed_range.mem_of_tendsto (hcoord n)
      (Eventually.of_forall fun l => mem_range_self (q l n))
  choose p hp using hex
  have hqp : Tendsto q atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro n
    apply (A n).closedEmbedding_j.tendsto_nhds_iff.mpr
    rw [hp n]
    exact hcoord n
  refine ⟨p, tendsto_nhds_unique ?_ hz⟩
  exact ((continuous_family A).tendsto p |>.comp hqp).congr'
    (Eventually.of_forall hq)

theorem isClosedEmbedding_family (A : ℕ → AdmissibleFamily) :
    IsClosedEmbedding (family A) :=
  ⟨isEmbedding_family A, isClosed_range_family A⟩

def separator (A : ℕ → AdmissibleFamily) (i : ℕ × ℕ) : Fock →L[ℝ] ℝ :=
  ((A i.1).separator i.2).comp (recover A i.1)

@[simp] theorem separator_family (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ × ℕ) :
    separator A i (family A q) = (A i.1).separator i.2 ((A i.1).j (q i.1)) := by
  simp only [separator, ContinuousLinearMap.comp_apply, recover_family]

theorem locallyConstant_separator (A : ℕ → AdmissibleFamily) (i : ℕ × ℕ) :
    IsLocallyConstant (separator A i ∘ family A) := by
  simpa only [Function.comp_def, separator_family] using
    ((A i.1).locallyConstant_separator i.2).comp_continuous (continuous_apply i.1)

theorem separates (A : ℕ → AdmissibleFamily) (p q : Parameter A) (hpq : p ≠ q) :
    ∃ i, separator A i (family A p) ≠ separator A i (family A q) := by
  have hn : ∃ n, p n ≠ q n := Function.ne_iff.mp hpq
  obtain ⟨n, hn⟩ := hn
  obtain ⟨k, hk⟩ := (A n).separates (p n) (q n) hn
  exact ⟨(n, k), by simpa only [separator_family] using hk⟩

end NoUniversalFSigma.TensorFamily
end
end

/- Source module: NoUniversalFSigma.AugmentedPackets -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Set

namespace NoUniversalFSigma.FiniteL2

abbrev FlatIndex := Σ F : Finset ℕ, F → ℕ

def extendAssignment (B : Finset ℕ) (a : B → Option ℕ) (n : ℕ) : Option ℕ :=
  if h : n ∈ B then a ⟨n, h⟩ else none

@[simp] theorem extendAssignment_apply (B : Finset ℕ) (a : B → Option ℕ) (n : B) :
    extendAssignment B a n = a n := by simp [extendAssignment, n.property]

def selectedSupport (B : Finset ℕ) (a : B → Option ℕ) : Finset ℕ :=
  B.filter (fun n => (extendAssignment B a n).isSome)

theorem selectedSupport_subset (B : Finset ℕ) (a : B → Option ℕ) : selectedSupport B a ⊆ B :=
  Finset.filter_subset _ _

/-- An augmented coordinate chooses exactly the finite subset carrying `some` labels. -/
def encodeAugmentedIndex (B : Finset ℕ) (a : B → Option ℕ) : FlatIndex :=
  ⟨selectedSupport B a, fun n => (extendAssignment B a n).getD 0⟩

def decodeAugmentedIndex (B : Finset ℕ) (p : FlatIndex) (n : B) : Option ℕ :=
  if h : n.val ∈ p.1 then some (p.2 ⟨n.val, h⟩) else none

@[simp] theorem decode_encodeAugmentedIndex (B : Finset ℕ) (a : B → Option ℕ) :
    decodeAugmentedIndex B (encodeAugmentedIndex B a) = a := by
  funext n
  cases ha : a n with
  | none =>
    have hs : n.val ∉ selectedSupport B a := by
      simp [selectedSupport, extendAssignment, n.property, ha]
    simp [decodeAugmentedIndex, encodeAugmentedIndex, hs, ha]
  | some k =>
    have hs : n.val ∈ selectedSupport B a := by
      simp [selectedSupport, extendAssignment, n.property, ha]
    simp [decodeAugmentedIndex, encodeAugmentedIndex, hs, extendAssignment, n.property, ha]

theorem encodeAugmentedIndex_injective (B : Finset ℕ) :
    Function.Injective (encodeAugmentedIndex B) := by
  intro a b h
  have he := congrArg (decodeAugmentedIndex B) h
  simpa only [decode_encodeAugmentedIndex] using he

theorem encodeAugmentedIndex_subset (B : Finset ℕ) (a : B → Option ℕ) :
    (encodeAugmentedIndex B a).1 ⊆ B := selectedSupport_subset B a

theorem augmentedAtom_apply_encode (B : Finset ℕ) (v : ℕ → RealL2) (a : B → Option ℕ) :
    augmentedAtom B v a = atom (encodeAugmentedIndex B a).1 v (encodeAugmentedIndex B a).2 := by
  let f : ℕ → ℝ := fun n => (extendAssignment B a n).elim 1 (fun k => v n k)
  have hfull : augmentedAtom B v a = ∏ n ∈ B, f n := by
    rw [augmentedAtom_apply]
    calc
      _ = ∏ n : B, f n := by
        apply Finset.prod_congr rfl
        intro n _
        simp only [f, extendAssignment_apply]
      _ = _ := Finset.prod_coe_sort _ _
  have hselected : (∏ n ∈ selectedSupport B a, f n) = ∏ n ∈ B, f n := by
    apply Finset.prod_subset (selectedSupport_subset B a)
    intro n hn hnot
    have hnnone : extendAssignment B a n = none := by
      cases he : extendAssignment B a n with
      | none => rfl
      | some k => exact (hnot (Finset.mem_filter.2 ⟨hn, by simp [he]⟩)).elim
    simp [f, hnnone]
  rw [hfull, ← hselected, atom_apply]
  change (∏ n ∈ selectedSupport B a, f n) =
    ∏ n : selectedSupport B a, v n ((extendAssignment B a n).getD 0)
  rw [← Finset.prod_coe_sort (selectedSupport B a) f]
  apply Finset.prod_congr rfl
  intro n _
  have hn := (Finset.mem_filter.1 n.property).2
  cases he : extendAssignment B a n with
  | none => simp [he] at hn
  | some k => simp only [f, he, Option.elim_some, Option.getD_some]

/-- Projection onto the entire finite packet, including every subset coordinate. -/
def augmentedProjection (B : Finset ℕ) : L2Coordinates.L2 FlatIndex →L[ℝ] AugmentedPacket B :=
  L2Coordinates.restrictCLM (encodeAugmentedIndex B) (encodeAugmentedIndex_injective B)

@[simp] theorem augmentedProjection_apply (B : Finset ℕ) (x : L2Coordinates.L2 FlatIndex)
    (a : B → Option ℕ) : augmentedProjection B x a = x (encodeAugmentedIndex B a) := rfl

theorem augmentedProjection_eq_atom (B : Finset ℕ) (x : L2Coordinates.L2 FlatIndex)
    (v : ℕ → RealL2)
    (hx : ∀ p : FlatIndex, x p = atom p.1 v p.2) :
    augmentedProjection B x = augmentedAtom B v := by
  ext a
  rw [augmentedProjection_apply, hx, augmentedAtom_apply_encode]

theorem norm_augmentedProjection_le (B : Finset ℕ) (x : L2Coordinates.L2 FlatIndex) :
    ‖augmentedProjection B x‖ ≤ ‖x‖ :=
  L2Coordinates.norm_restrict_le (encodeAugmentedIndex B) (encodeAugmentedIndex_injective B) x

end NoUniversalFSigma.FiniteL2
end
end

/- Source module: NoUniversalFSigma.FockSplit -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Set Topology

namespace NoUniversalFSigma.FiniteL2
open L2Coordinates

def flatFunction (p : FlatIndex) (n : ℕ) : Option ℕ :=
  if h : n ∈ p.1 then some (p.2 ⟨n, h⟩) else none

@[simp] theorem flatFunction_ne_none_iff (p : FlatIndex) (n : ℕ) :
    flatFunction p n ≠ none ↔ n ∈ p.1 := by
  simp only [flatFunction]
  split_ifs <;> simp_all

theorem flatIndex_ext {p q : FlatIndex} (h : ∀ n, flatFunction p n = flatFunction q n) : p = q := by
  have hs : p.1 = q.1 := by
    ext n
    rw [← flatFunction_ne_none_iff, ← flatFunction_ne_none_iff, h n]
  obtain ⟨F, a⟩ := p
  obtain ⟨G, b⟩ := q
  dsimp at hs
  subst G
  apply congrArg (Sigma.mk F)
  funext n
  have he := h n
  simpa only [flatFunction, dif_pos n.property, Option.some.injEq] using he

theorem flatFunction_encode (B : Finset ℕ) (a : B → Option ℕ) (n : ℕ) :
    flatFunction (encodeAugmentedIndex B a) n = extendAssignment B a n := by
  by_cases hn : n ∈ B
  · cases ha : a ⟨n, hn⟩ with
    | none => simp [flatFunction, encodeAugmentedIndex, selectedSupport, extendAssignment, hn, ha]
    | some k => simp [flatFunction, encodeAugmentedIndex, selectedSupport, extendAssignment, hn, ha]
  · simp [flatFunction, encodeAugmentedIndex, selectedSupport, extendAssignment, hn]

def unionIndex (p q : FlatIndex) (h : Disjoint p.1 q.1) : FlatIndex :=
  ⟨p.1 ∪ q.1, Equiv.piFinsetUnion (fun _ : ℕ => ℕ) h (p.2, q.2)⟩

theorem flatFunction_union_left (p q : FlatIndex) (h : Disjoint p.1 q.1)
    (n : ℕ) (hn : n ∉ q.1) : flatFunction (unionIndex p q h) n = flatFunction p n := by
  by_cases hp : n ∈ p.1
  · have hmem : n ∈ p.1 ∪ q.1 := Finset.mem_union_left _ hp
    simp only [flatFunction, unionIndex, dif_pos hmem, dif_pos hp]
    rw [Equiv.piFinsetUnion_left (fun _ : ℕ => ℕ) h hp hmem]
  · have hmem : n ∉ p.1 ∪ q.1 := by simp [hp, hn]
    simp only [flatFunction, unionIndex, dif_neg hmem, dif_neg hp]

theorem flatFunction_union_right (p q : FlatIndex) (h : Disjoint p.1 q.1)
    (n : ℕ) (hn : n ∉ p.1) : flatFunction (unionIndex p q h) n = flatFunction q n := by
  by_cases hq : n ∈ q.1
  · have hmem : n ∈ p.1 ∪ q.1 := Finset.mem_union_right _ hq
    simp only [flatFunction, unionIndex, dif_pos hmem, dif_pos hq]
    rw [Equiv.piFinsetUnion_right (fun _ : ℕ => ℕ) h hq hmem]
  · have hmem : n ∉ p.1 ∪ q.1 := by simp [hn, hq]
    simp only [flatFunction, unionIndex, dif_neg hmem, dif_neg hq]

def outsideIndex (B : Finset ℕ) (p : FlatIndex) : FlatIndex :=
  ⟨p.1 \ B, fun n => p.2 ⟨n, (Finset.mem_sdiff.1 n.property).1⟩⟩

theorem outsideIndex_disjoint (B : Finset ℕ) (p : FlatIndex) :
    Disjoint (outsideIndex B p).1 B :=
  Finset.disjoint_left.2 (fun _ hn hB => (Finset.mem_sdiff.1 hn).2 hB)

theorem flatFunction_outside (B : Finset ℕ) (p : FlatIndex) (n : ℕ) :
    flatFunction (outsideIndex B p) n = if n ∈ B then none else flatFunction p n := by
  by_cases hnB : n ∈ B <;> by_cases hnP : n ∈ p.1 <;>
    simp [flatFunction, outsideIndex, Finset.mem_sdiff, hnB, hnP]

/-- Tail indices are square-free coordinate sets disjoint from the finite block. -/
abbrev TailIndex (B : Finset ℕ) := {p : FlatIndex // Disjoint p.1 B}

def splitTail (B : Finset ℕ) (p : FlatIndex) : TailIndex B :=
  ⟨outsideIndex B p, outsideIndex_disjoint B p⟩

theorem encode_disjoint_tail (B : Finset ℕ) (a : B → Option ℕ) (t : TailIndex B) :
    Disjoint (encodeAugmentedIndex B a).1 t.val.1 := by
  apply Finset.disjoint_left.2
  intro n hn ht
  exact Finset.disjoint_left.1 t.property ht (encodeAugmentedIndex_subset B a hn)

def joinSplitIndex (B : Finset ℕ) (a : B → Option ℕ) (t : TailIndex B) : FlatIndex :=
  unionIndex (encodeAugmentedIndex B a) t.val (encode_disjoint_tail B a t)

theorem flatFunction_join_inside (B : Finset ℕ) (a : B → Option ℕ) (t : TailIndex B)
    (n : ℕ) (hn : n ∈ B) : flatFunction (joinSplitIndex B a t) n = a ⟨n, hn⟩ := by
  have ht : n ∉ t.val.1 := fun ht => Finset.disjoint_left.1 t.property ht hn
  rw [joinSplitIndex, flatFunction_union_left _ _ _ n ht, flatFunction_encode]
  simp only [extendAssignment, dif_pos hn]

theorem flatFunction_join_outside (B : Finset ℕ) (a : B → Option ℕ) (t : TailIndex B)
    (n : ℕ) (hn : n ∉ B) : flatFunction (joinSplitIndex B a t) n = flatFunction t.val n := by
  have ha : n ∉ (encodeAugmentedIndex B a).1 := fun ha => hn (encodeAugmentedIndex_subset B a ha)
  exact flatFunction_union_right _ _ _ n ha

theorem joinSplitIndex_split (B : Finset ℕ) (p : FlatIndex) :
    joinSplitIndex B (decodeAugmentedIndex B p) (splitTail B p) = p := by
  apply flatIndex_ext
  intro n
  by_cases hn : n ∈ B
  · rw [flatFunction_join_inside B _ _ n hn]
    rfl
  · rw [flatFunction_join_outside B _ _ n hn]
    simp only [splitTail, flatFunction_outside, if_neg hn]

theorem decode_joinSplitIndex (B : Finset ℕ) (a : B → Option ℕ) (t : TailIndex B) :
    decodeAugmentedIndex B (joinSplitIndex B a t) = a := by
  funext n
  exact flatFunction_join_inside B a t n n.property

theorem outside_joinSplitIndex (B : Finset ℕ) (a : B → Option ℕ) (t : TailIndex B) :
    outsideIndex B (joinSplitIndex B a t) = t.val := by
  apply flatIndex_ext
  intro n
  rw [flatFunction_outside]
  by_cases hn : n ∈ B
  · rw [if_pos hn]
    have ht : n ∉ t.val.1 := fun ht => Finset.disjoint_left.1 t.property ht hn
    simp only [flatFunction, dif_neg ht]
  · rw [if_neg hn, flatFunction_join_outside B a t n hn]

/-- The exact finite-block/tail splitting of the square-free Fock coordinate set. -/
def splitIndex (B : Finset ℕ) : FlatIndex ≃ (B → Option ℕ) × TailIndex B where
  toFun p := (decodeAugmentedIndex B p, splitTail B p)
  invFun p := joinSplitIndex B p.1 p.2
  left_inv := joinSplitIndex_split B
  right_inv p := Prod.ext (decode_joinSplitIndex B p.1 p.2)
    (Subtype.ext (outside_joinSplitIndex B p.1 p.2))

def split (B : Finset ℕ) : L2 FlatIndex ≃ₗᵢ[ℝ] MatrixL2 (B → Option ℕ) (TailIndex B) :=
  reindex (splitIndex B)

@[simp] theorem split_apply (B : Finset ℕ) (x : L2 FlatIndex)
    (a : B → Option ℕ) (t : TailIndex B) :
    split B x (a, t) = x (joinSplitIndex B a t) := rfl

def tailRestriction (B : Finset ℕ) : L2 FlatIndex →L[ℝ] L2 (TailIndex B) :=
  restrictCLM Subtype.val Subtype.val_injective

@[simp] theorem tailRestriction_apply (B : Finset ℕ) (x : L2 FlatIndex) (t : TailIndex B) :
    tailRestriction B x t = x t.val := rfl

theorem atom_unionIndex (p q : FlatIndex) (h : Disjoint p.1 q.1) (v : ℕ → RealL2) :
    atom (unionIndex p q h).1 v (unionIndex p q h).2 =
      atom p.1 v p.2 * atom q.1 v q.2 := by
  have he := congrArg (fun x : MatrixL2 (p.1 → ℕ) (q.1 → ℕ) => x (p.2, q.2))
    (packetUnion_atom p.1 q.1 h v)
  simpa only [packetUnion_apply, outer_apply, unionIndex] using he

theorem split_factorization (B : Finset ℕ) (x : L2 FlatIndex) (v : ℕ → RealL2)
    (hx : ∀ p : FlatIndex, x p = atom p.1 v p.2) :
    split B x = outer (augmentedAtom B v) (tailRestriction B x) := by
  ext p
  obtain ⟨a, t⟩ := p
  rw [split_apply, outer_apply, tailRestriction_apply, hx, hx,
    augmentedAtom_apply_encode]
  exact atom_unionIndex _ _ _ _

/-- Reassembling a coefficient packet and a tail is a continuous bilinear operation. -/
def merge (B : Finset ℕ) (v : AugmentedPacket B) (w : L2 (TailIndex B)) : L2 FlatIndex :=
  (split B).symm (outer v w)

theorem norm_merge (B : Finset ℕ) (v : AugmentedPacket B) (w : L2 (TailIndex B)) :
    ‖merge B v w‖ = ‖v‖ * ‖w‖ := by rw [merge, LinearIsometryEquiv.norm_map, norm_outer]

theorem continuous_merge (B : Finset ℕ) :
    Continuous (fun p : AugmentedPacket B × L2 (TailIndex B) => merge B p.1 p.2) :=
  (split B).symm.continuous.comp continuous_outer

theorem merge_factorization (B : Finset ℕ) (x : L2 FlatIndex) (v : ℕ → RealL2)
    (hx : ∀ p : FlatIndex, x p = atom p.1 v p.2) :
    merge B (augmentedAtom B v) (tailRestriction B x) = x := by
  rw [merge, ← split_factorization B x v hx, LinearIsometryEquiv.symm_apply_apply]

end NoUniversalFSigma.FiniteL2
end
end

/- Source module: NoUniversalFSigma.TensorEscape -/
section
noncomputable section
open scoped BigOperators
open Set Topology

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2

def augmentedSingletonIndex (i : ℕ) : (({i} : Finset ℕ) → Option ℕ) ≃ Option ℕ where
  toFun a := a ⟨i, Finset.mem_singleton_self i⟩
  invFun a := fun _ => a
  left_inv a := by
    funext n
    have hn : n = ⟨i, Finset.mem_singleton_self i⟩ := Subtype.ext (Finset.mem_singleton.1 n.property)
    simp only [hn]
  right_inv _ := rfl

def augmentedSingleton (i : ℕ) : AugmentedPacket {i} ≃ₗᵢ[ℝ] L2 (Option ℕ) :=
  reindex (augmentedSingletonIndex i)

def insertionCoefficient (A : ℕ → AdmissibleFamily) (i : ℕ) : RealL2 →L[ℝ] AugmentedPacket {i} :=
  (augmentedSingleton i).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (augmentCLM.comp ((A i).mass.prod ((weight A i) • ContinuousLinearMap.id ℝ RealL2)))

theorem insertionCoefficient_apply (A : ℕ → AdmissibleFamily) (i : ℕ)
    (v : RealL2) (a : ({i} : Finset ℕ) → Option ℕ) :
    insertionCoefficient A i v a = (a ⟨i, Finset.mem_singleton_self i⟩).elim
      ((A i).mass v) (fun n => weight A i * v n) := rfl

def insertion (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ) : RealL2 →L[ℝ] Fock :=
  (FiniteL2.split {i}).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((outerBilinear.flip (tailRestriction {i} (family A q))).comp (insertionCoefficient A i))

theorem insertion_apply (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ) (v : RealL2) :
    insertion A q i v = merge {i} (insertionCoefficient A i v) (tailRestriction {i} (family A q)) := rfl

theorem merge_coordinate (B : Finset ℕ) (v : AugmentedPacket B)
    (w : L2 (TailIndex B)) (p : FlatIndex) :
    merge B v w p = v (decodeAugmentedIndex B p) * w (splitTail B p) := rfl

theorem continuous_insertParameter (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ) :
    Continuous (fun t : (A i).Parameter => Function.update q i t) := by
  apply continuous_pi
  intro n
  by_cases hn : n = i
  · subst n
    simpa only [Function.update_self] using (continuous_id : Continuous (fun t : (A i).Parameter => t))
  · simpa only [Function.update_of_ne hn] using (continuous_const : Continuous (fun _ : (A i).Parameter => q n))

theorem tailRestriction_update (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ)
    (t : (A i).Parameter) :
    tailRestriction {i} (family A (Function.update q i t)) = tailRestriction {i} (family A q) := by
  ext p
  obtain ⟨⟨F, a⟩, hd⟩ := p
  change family A (Function.update q i t) ⟨F, a⟩ = family A q ⟨F, a⟩
  rw [family_apply, family_apply]
  apply Finset.prod_congr rfl
  intro n _
  have hn : (n : ℕ) ≠ i := by
    intro h
    exact Finset.disjoint_left.1 hd n.property (by simp [h])
  rw [Function.update_of_ne hn]

theorem insertionCoefficient_family (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ)
    (t : (A i).Parameter) :
    insertionCoefficient A i ((A i).j t) =
      augmentedAtom {i} (fun n => weight A n • (A n).j (Function.update q i t n)) := by
  ext a
  rw [insertionCoefficient_apply, (A i).mass_j]
  rw [augmentedAtom_apply]
  have he : (∏ n : ({i} : Finset ℕ), (a n).elim 1
      (fun k => (weight A n • (A n).j (Function.update q i t n)) k)) =
      (a ⟨i, Finset.mem_singleton_self i⟩).elim 1 (fun k => weight A i * (A i).j t k) := by
    have hidx : (default : ({i} : Finset ℕ)) = ⟨i, Finset.mem_singleton_self i⟩ :=
      Subtype.ext (Finset.mem_singleton.1 (default : ({i} : Finset ℕ)).property)
    rw [Fintype.prod_unique, hidx]
    simp only [Function.update_self]
    rfl
  exact he.symm

theorem insertion_family (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ)
    (t : (A i).Parameter) :
    insertion A q i ((A i).j t) = family A (Function.update q i t) := by
  rw [insertion_apply, insertionCoefficient_family A q i t, ← tailRestriction_update A q i t]
  apply merge_factorization
  intro p
  obtain ⟨F, a⟩ := p
  simp only [atom_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  exact family_apply A _ F a

theorem recover_mem_span (A : ℕ → AdmissibleFamily) (i : ℕ) {v : Fock}
    (hv : v ∈ Submodule.span ℝ (range (family A))) : recover A i v ∈ (A i).span := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨q, rfl⟩ := hx
    rw [recover_family]
    exact (A i).j_mem_span _
  | zero => simpa only [map_zero] using (A i).span.zero_mem
  | add x y hx hy ihx ihy => simpa only [map_add] using (A i).span.add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using (A i).span.smul_mem a ih

theorem singleton_apply (i : ℕ) (v : Fock) (k : ℕ) :
    singleton i v k = v ⟨{i}, fun _ => k⟩ := rfl

theorem recover_insertion (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ) (v : RealL2) :
    recover A i (insertion A q i v) = v := by
  ext k
  change (weight A i)⁻¹ * singleton i (insertion A q i v) k = v k
  rw [singleton_apply, insertion_apply, merge_coordinate, insertionCoefficient_apply]
  have hinside : decodeAugmentedIndex {i} (⟨{i}, fun _ => k⟩ : FlatIndex)
      ⟨i, Finset.mem_singleton_self i⟩ = some k := by simp [decodeAugmentedIndex]
  rw [hinside]
  simp only [Option.elim_some, tailRestriction_apply]
  haveI : IsEmpty ↥((splitTail {i} (⟨{i}, fun _ => k⟩ : FlatIndex)).val.1) := by
    constructor
    intro n
    have hn := n.property
    simpa only [splitTail, outsideIndex, Finset.sdiff_self, Finset.notMem_empty] using hn
  rw [family_apply]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [← mul_assoc, inv_mul_cancel₀ (weight_ne_zero A i), one_mul]

theorem insertion_preserves_escape (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ)
    {v : RealL2} (hv : v ∉ (A i).span) :
    insertion A q i v ∉ Submodule.span ℝ (range (family A)) := by
  intro h
  exact hv (by rw [← recover_insertion A q i v]; exact recover_mem_span A i h)

theorem rank_transfer_factor (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ) (α : Ordinal)
    {t u : (A i).Parameter} (h : (t, u) ∈ escapeRemainder ((A i).span : Set RealL2) (A i).j α) :
    (Function.update q i t, Function.update q i u) ∈
      escapeRemainder (Submodule.span ℝ (range (family A)) : Set Fock) (family A) α := by
  apply escapeRemainder_transfer
      (Submodule.span ℝ (range (family A)) : Set Fock) ((A i).span : Set RealL2)
      (family A) (A i).j (fun t => Function.update q i t) (fun t => Function.update q i t)
      (continuous_insertParameter A q i) (continuous_insertParameter A q i)
      (insertion A q i) (insertion A q i).continuous ?_ ?_ α
      (Set.mem_image_of_mem _ h)
  · intro s r
    simp only [pairSum, map_add, insertion_family]
  · intro z hz
    exact insertion_preserves_escape A q i hz

theorem diagonal_rank_of_factor (A : ℕ → AdmissibleFamily) (q : Parameter A) (i : ℕ)
    (α : Ordinal.{0}) (h : (A i).HasDiagonalRank α) :
    (q, q) ∈ escapeRemainder (Submodule.span ℝ (range (family A)) : Set Fock) (family A) α := by
  have he := rank_transfer_factor A q i α (h (q i))
  simpa only [Function.update_eq_self] using he

end NoUniversalFSigma.TensorFamily
end
end

/- Source module: NoUniversalFSigma.OrdinalRanks -/
section
noncomputable section
open Set Ordinal

namespace NoUniversalFSigma

/-- A nonzero countable limit ordinal has an increasing countable cofinal
sequence of smaller countable ordinals. -/
theorem exists_countable_cofinal_sequence {ζ : Ordinal.{0}}
    (hζ : Order.IsSuccLimit ζ) (hcount : ζ < ω₁) :
    ∃ a : ℕ → Ordinal.{0}, StrictMono a ∧ (∀ n, a n < ζ) ∧
      (∀ ξ < ζ, ∃ n, ξ ≤ a n) ∧ (⨆ n, a n) = ζ := by
  have hcof : ζ.cof.ord = ω := by
    rw [Ordinal.cof_eq_aleph0_of_isSuccLimit hζ hcount, Cardinal.ord_aleph0]
  obtain ⟨f, hf⟩ := Ordinal.exists_isFundamentalSeq hcof
  let a : ℕ → Ordinal.{0} := fun n => (f ⟨n, natCast_lt_omega0 n⟩).val
  have ha : ∀ n, a n < ζ := fun n => (f ⟨n, natCast_lt_omega0 n⟩).property
  have hmono : StrictMono a := by
    intro i j hij
    apply hf.strictMono
    change (i : Ordinal) < (j : Ordinal)
    exact_mod_cast hij
  have hcofinal : ∀ ξ < ζ, ∃ n, ξ ≤ a n := by
    intro ξ hξ
    obtain ⟨y, ⟨d, rfl⟩, hd⟩ := hf.isCofinal_range ⟨ξ, hξ⟩
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp d.property
    refine ⟨n, ?_⟩
    have heq : d = (⟨n, natCast_lt_omega0 n⟩ : Set.Iio ω) := Subtype.ext hn
    simpa only [heq] using hd
  refine ⟨a, hmono, ha, hcofinal, le_antisymm (Ordinal.iSup_le (fun n => (ha n).le)) ?_⟩
  apply le_of_forall_lt
  intro ξ hξ
  obtain ⟨n, hn⟩ := hcofinal (ξ + 1) (hζ.add_one_lt hξ)
  exact (lt_add_one ξ).trans_le (hn.trans (Ordinal.le_iSup a n))

/-- Survival at a cofinal sequence of stages implies survival at a limit stage. -/
theorem derivativeIter_mem_limit_of_cofinal {X : Type*} (D : Set X →o Set X) (A : Set X)
    {ζ : Ordinal} (hζ : Order.IsSuccLimit ζ) (a : ℕ → Ordinal)
    (hcofinal : ∀ ξ < ζ, ∃ n, ξ ≤ a n) {x : X}
    (hx : ∀ n, x ∈ derivativeIter D A (a n)) : x ∈ derivativeIter D A ζ := by
  rw [derivativeIter_limit D A hζ]
  apply mem_iInter.mpr
  intro ξ
  obtain ⟨n, hn⟩ := hcofinal ξ.val ξ.property
  exact derivativeIter_antitone D A hn (hx n)

/-- The corresponding limit-survival rule for source escape remainders. -/
theorem escapeRemainder_mem_limit_of_cofinal {P B : Type*}
    [TopologicalSpace P] [TopologicalSpace B] [Add B]
    (H : Set B) (j : P → B) {ζ : Ordinal} (hζ : Order.IsSuccLimit ζ)
    (a : ℕ → Ordinal) (hcofinal : ∀ ξ < ζ, ∃ n, ξ ≤ a n) {p : P × P}
    (hp : ∀ n, p ∈ escapeRemainder H j (a n)) : p ∈ escapeRemainder H j ζ :=
  derivativeIter_mem_limit_of_cofinal (escapeOperator H j) Set.univ hζ a hcofinal hp

end NoUniversalFSigma


namespace NoUniversalFSigma
open Ordinal

/-- Transfinite induction through the countable ordinals with a countable
cofinal sequence supplied at every nonzero limit stage. -/
theorem countableOrdinal_induction (Q : Ordinal.{0} → Prop) (hzero : Q 0)
    (hsucc : ∀ ξ, ξ < ω₁ → Q ξ → Q (ξ + 1))
    (hlimit : ∀ ζ, ζ < ω₁ → Order.IsSuccLimit ζ →
      ∀ a : ℕ → Ordinal.{0}, (∀ n, a n < ζ) →
        (∀ ξ < ζ, ∃ n, ξ ≤ a n) → (∀ n, Q (a n)) → Q ζ) :
    ∀ ξ, ξ < ω₁ → Q ξ := by
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
    intro hξ
    rcases Ordinal.zero_or_succ_or_isSuccLimit ξ with hzero' | ⟨η, rfl⟩ | hlim
    · exact hzero' ▸ hzero
    · have hη : η < Order.succ η := by simpa only [Order.succ_eq_add_one] using lt_add_one η
      simpa only [Order.succ_eq_add_one] using hsucc η (hη.trans hξ) (IH η hη (hη.trans hξ))
    · obtain ⟨a, hmono, ha, hcofinal, hsup⟩ := exists_countable_cofinal_sequence hlim hξ
      exact hlimit ξ hξ hlim a ha hcofinal (fun n => IH (a n) (ha n) ((ha n).trans hξ))

end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.LimitRank -/
section
noncomputable section
open Set Ordinal

namespace NoUniversalFSigma.TensorFamily

/-- The countable tensor construction preserves every rank in a cofinal list
and therefore reaches their limit. This is the rank part of Lemma 7.3. -/
theorem diagonal_rank_limit (A : ℕ → AdmissibleFamily) (a : ℕ → Ordinal.{0})
    {ζ : Ordinal.{0}} (hζ : Order.IsSuccLimit ζ)
    (hcofinal : ∀ ξ < ζ, ∃ n, ξ ≤ a n)
    (hA : ∀ n, HasDiagonalRank (A n) (a n)) :
    ∀ q, (q, q) ∈ escapeRemainder
      (Submodule.span ℝ (range (family A)) : Set Fock) (family A) ζ := by
  intro q
  exact escapeRemainder_mem_limit_of_cofinal _ _ hζ a hcofinal
    (fun n => diagonal_rank_of_factor A q n (a n) (hA n))

end NoUniversalFSigma.TensorFamily
end
end

/- Source module: NoUniversalFSigma.LimitFamily -/
section
/-!
# Packaging the genuine countable tensor family

The constructor in this file takes the algebraic-span `Fσ` proof explicitly.
Its remaining fields are supplied by the concrete tensor and coordinate modules.
The closed-chart theorem is intended to supply that argument at the call site.
-/

noncomputable section
open Set
open scoped BigOperators

namespace NoUniversalFSigma

/-- The genuine Fock family with an explicit certificate for its algebraic span. -/
def tensorHilbertFamily (A : ℕ → AdmissibleFamily)
    (hspan : IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock)) :
    HilbertFamily TensorFamily.Fock :=
  HilbertFamily.ofCountableSeparators (TensorFamily.family A)
    (∑' F, TensorFamily.envelope F) (TensorFamily.norm_family_le A)
    (TensorFamily.continuous_family A) (TensorFamily.isClosedEmbedding_family A)
    TensorFamily.mass (TensorFamily.mass_family A)
    (TensorFamily.separator A) (TensorFamily.locallyConstant_separator A)
    (TensorFamily.separates A) hspan

/-- The countable tensor family embedded in the fixed real `ℓ²`. -/
def limitFamily (A : ℕ → AdmissibleFamily)
    (hspan : IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock)) :
    AdmissibleFamily := normalizeFamily (tensorHilbertFamily A hspan)

theorem tensorHilbertFamily_hasDiagonalRank_of_factor (A : ℕ → AdmissibleFamily)
    (hspan : IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock))
    (i : ℕ) (α : Ordinal.{0}) (h : (A i).HasDiagonalRank α) :
    (tensorHilbertFamily A hspan).HasDiagonalRank α :=
  fun q => TensorFamily.diagonal_rank_of_factor A q i α h

theorem limitFamily_hasDiagonalRank_of_factor (A : ℕ → AdmissibleFamily)
    (hspan : IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock))
    (i : ℕ) (α : Ordinal.{0}) (h : (A i).HasDiagonalRank α) :
    (limitFamily A hspan).HasDiagonalRank α :=
  normalizeFamily_hasDiagonalRank (tensorHilbertFamily A hspan) α
    (tensorHilbertFamily_hasDiagonalRank_of_factor A hspan i α h)

theorem tensorHilbertFamily_hasDiagonalRank_limit (A : ℕ → AdmissibleFamily)
    (hspan : IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock))
    (a : ℕ → Ordinal.{0}) {ζ : Ordinal.{0}} (hζ : Order.IsSuccLimit ζ)
    (hcofinal : ∀ ξ < ζ, ∃ n, ξ ≤ a n)
    (hA : ∀ n, (A n).HasDiagonalRank (a n)) :
    (tensorHilbertFamily A hspan).HasDiagonalRank ζ :=
  TensorFamily.diagonal_rank_limit A a hζ hcofinal hA

theorem limitFamily_hasDiagonalRank_limit (A : ℕ → AdmissibleFamily)
    (hspan : IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock))
    (a : ℕ → Ordinal.{0}) {ζ : Ordinal.{0}} (hζ : Order.IsSuccLimit ζ)
    (hcofinal : ∀ ξ < ζ, ∃ n, ξ ≤ a n)
    (hA : ∀ n, (A n).HasDiagonalRank (a n)) :
    (limitFamily A hspan).HasDiagonalRank ζ :=
  normalizeFamily_hasDiagonalRank (tensorHilbertFamily A hspan) ζ
    (tensorHilbertFamily_hasDiagonalRank_limit A hspan a hζ hcofinal hA)

end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.Category -/
section
/-!
# Category preliminaries

This file proves the continuous-restriction lemma and the elementary category
facts used in Section 2.3 of arXiv:2610.31052.
-/

open Set Filter Topology TopologicalSpace

namespace NoUniversalFSigma

universe u v

/-- Lemma 2.4: a Baire-measurable map with second-countable target is
continuous on a comeager `Gδ` subspace of a Polish space. -/
theorem baire_measurable_continuous_on_comeagre_gdelta {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    (f : X → Y) (hf : IsBaireMeasurable f) :
    ∃ C : Set X, IsGδ C ∧ IsMeagre Cᶜ ∧ Continuous (fun x : C => f x) := by
  classical
  have happrox (U : countableBasis Y) :
      ∃ V : Set X, IsOpen V ∧ (f ⁻¹' (U : Set Y)) =ᵇ V :=
    (hf U (isOpen_of_mem_countableBasis U.property)).residualEq_isOpen
  choose V hV hEq using happrox
  have hsim : ∀ᶠ x in residual X,
      ∀ U : countableBasis Y, f x ∈ (U : Set Y) ↔ x ∈ V U := by
    apply eventually_countable_forall.mpr
    intro U
    exact eventuallyEq_set.mp (hEq U)
  obtain ⟨C, hC, hCd, hCp⟩ := eventually_residual.mp hsim
  refine ⟨C, hC, ?_, ?_⟩
  · simpa only [IsMeagre, compl_compl] using residual_of_dense_Gδ hC hCd
  · apply (isBasis_countableBasis Y).continuous_iff.mpr
    intro U hU
    have hpre : (fun x : C => f x) ⁻¹' U =
        (Subtype.val : C → X) ⁻¹' V ⟨U, hU⟩ := by
      ext x
      exact hCp x x.property ⟨U, hU⟩
    rw [hpre]
    exact (hV ⟨U, hU⟩).preimage continuous_subtype_val

/-- Lemma 2.5(1). -/
theorem baireSpace_of_dense_gdelta {X : Type u} [TopologicalSpace X]
    [BaireSpace X] {C : Set X} (hC : IsGδ C) (hd : Dense C) : BaireSpace C :=
  hC.baireSpace_of_dense hd

/-- Lemma 2.5(2), in the dense-open form. -/
theorem dense_open_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y}
    (hp : Continuous p) (hpo : IsOpenMap p) {U : Set Y}
    (hU : IsOpen U) (hd : Dense U) :
    IsOpen (p ⁻¹' U) ∧ Dense (p ⁻¹' U) :=
  ⟨hU.preimage hp, hd.preimage hpo⟩

/-- A continuous open map pulls comeager `Gδ` sets back to comeager `Gδ` sets. -/
theorem comeager_gdelta_preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y}
    (hp : Continuous p) (hpo : IsOpenMap p) {C : Set Y}
    (hC : IsGδ C) (hm : IsMeagre Cᶜ) :
    IsGδ (p ⁻¹' C) ∧ IsMeagre (p ⁻¹' C)ᶜ := by
  refine ⟨isGδ_induced hp hC, ?_⟩
  exact hm.preimage_of_isOpenMap hp hpo

/-- Countable intersections of comeager sets are comeager. -/
theorem comeager_iInter {X : Type u} [TopologicalSpace X]
    {ι : Sort v} [Countable ι] {C : ι → Set X}
    (hm : ∀ i, IsMeagre (C i)ᶜ) : IsMeagre (⋂ i, C i)ᶜ := by
  simp only [IsMeagre, compl_compl] at hm ⊢
  exact countable_iInter_mem.mpr hm

/-- Countable intersections preserve both the comeager and `Gδ` properties. -/
theorem comeager_gdelta_iInter {X : Type u} [TopologicalSpace X]
    {ι : Sort v} [Countable ι] {C : ι → Set X}
    (hC : ∀ i, IsGδ (C i)) (hm : ∀ i, IsMeagre (C i)ᶜ) :
    IsGδ (⋂ i, C i) ∧ IsMeagre (⋂ i, C i)ᶜ :=
  ⟨IsGδ.iInter hC, comeager_iInter hm⟩

/-- A comeager set meets every nonempty open set in a Baire space. -/
theorem comeager_inter_open_nonempty {X : Type u} [TopologicalSpace X]
    [BaireSpace X] {C U : Set X} (hm : IsMeagre Cᶜ)
    (hU : IsOpen U) (hne : U.Nonempty) : (C ∩ U).Nonempty := by
  have hr : C ∈ residual X := by simpa only [IsMeagre, compl_compl] using hm
  simpa only [inter_comm] using (dense_of_mem_residual hr).inter_open_nonempty U hU hne

/-- Homeomorphisms preserve comeager sets. -/
theorem comeager_image_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (h : X ≃ₜ Y) {C : Set X} (hm : IsMeagre Cᶜ) : IsMeagre (h '' C)ᶜ := by
  rw [h.image_eq_preimage_symm]
  exact hm.preimage_of_isOpenMap h.symm.continuous h.symm.isOpenMap

/-- In particular, translations in a topological additive group preserve
comeager sets, as in Lemma 2.5(3). -/
theorem comeager_image_add_right {X : Type u} [TopologicalSpace X]
    [AddGroup X] [IsTopologicalAddGroup X] (a : X) {C : Set X}
    (hm : IsMeagre Cᶜ) : IsMeagre ((fun x : X => x + a) '' C)ᶜ :=
  comeager_image_homeomorph (Homeomorph.addRight a) hm

/-- A countable list of translation requirements can be met simultaneously
inside any nonempty open set. This supplies the fixed first endpoint in the
comparison-of-derivatives argument. -/
theorem exists_mem_open_with_countably_many_translates
    {X : Type u} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X]
    [BaireSpace X] {ι : Sort v} [Countable ι]
    {C U : Set X} (hm : IsMeagre Cᶜ)
    (hU : IsOpen U) (hne : U.Nonempty) (a : ι → X) :
    ∃ v ∈ U, ∀ n, v - a n ∈ C := by
  have hr : C ∈ residual X := by simpa only [IsMeagre, compl_compl] using hm
  have htrans (n : ι) : ∀ᶠ v in residual X, v - a n ∈ C := by
    have ho : IsOpenMap (fun v : X => v - a n) := by
      simpa only [sub_eq_add_neg] using (Homeomorph.addRight (-a n)).isOpenMap
    exact tendsto_residual_of_isOpenMap (continuous_id.sub continuous_const) ho hr
  have hforall : ∀ᶠ v in residual X, ∀ n, v - a n ∈ C :=
    eventually_countable_forall.mpr htrans
  obtain ⟨v, hvU, hv⟩ :=
    (dense_of_mem_residual hforall).inter_open_nonempty U hU hne
  exact ⟨v, hvU, hv⟩

/-- A countable relatively closed cover of a dense `Gδ` subset of a
nonempty product is uniform on the trace of some nonempty open rectangle.
This is the category step in the rectangle lemma of Section 4. -/
theorem exists_open_rectangle_of_closed_cover
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [Nonempty Y] [BaireSpace (X × Y)]
    {D : Set (X × Y)} (hD : IsGδ D) (hd : Dense D)
    (A : ℕ → Set D) (hA : ∀ n, IsClosed (A n))
    (hcover : ⋃ n, A n = univ) :
    ∃ (n : ℕ) (U : Set X) (V : Set Y),
      IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧
        ∀ z : D, (z : X × Y) ∈ U ×ˢ V → z ∈ A n := by
  letI : BaireSpace D := hD.baireSpace_of_dense hd
  letI : Nonempty D := hd.nonempty.to_subtype
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hA hcover
  obtain ⟨W, hWo, hWeq⟩ :=
    isOpen_induced_iff.mp (isOpen_interior (s := A n))
  have hxW : (x : X × Y) ∈ W := by
    change x ∈ (Subtype.val : D → X × Y) ⁻¹' W
    rw [hWeq]
    exact hx
  obtain ⟨U, V, hU, hV, hxU, hxV, hUV⟩ :=
    isOpen_prod_iff.mp hWo x.val.1 x.val.2 hxW
  refine ⟨n, U, V, hU, hV, ⟨_, hxU⟩, ⟨_, hxV⟩, ?_⟩
  intro z hz
  apply interior_subset
  rw [← hWeq]
  exact hUV hz

/-- A closed condition on a relatively continuous map extends from a dense
set to all points of its domain lying in a prescribed ambient open set.
The larger domain need not itself be open or closed. -/
theorem closed_condition_of_dense_on_open
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {S D W : Set X} (hDS : D ⊆ S) (hd : Dense D) (hW : IsOpen W)
    {g : S → Y} (hg : Continuous g) {F : Set Y} (hF : IsClosed F)
    (hprop : ∀ z : S, (z : X) ∈ D ∩ W → g z ∈ F) :
    ∀ z : S, (z : X) ∈ W → g z ∈ F := by
  have hSD : Dense ((Subtype.val : S → X) ⁻¹' D) := by
    apply Subtype.dense_iff.mpr
    have hi : (Subtype.val : S → X) '' ((Subtype.val : S → X) ⁻¹' D) = D := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨⟨x, hDS hx⟩, hx, rfl⟩
    rw [hi, hd.closure_eq]
    exact subset_univ S
  have hsub : ((Subtype.val : S → X) ⁻¹' W) ∩
      ((Subtype.val : S → X) ⁻¹' D) ⊆ g ⁻¹' F := by
    intro z hz
    exact hprop z ⟨hz.2, hz.1⟩
  intro z hz
  exact closure_minimal hsub (hF.preimage hg)
    (hSD.open_subset_closure_inter (hW.preimage continuous_subtype_val) hz)

end NoUniversalFSigma

end

/- Source module: NoUniversalFSigma.Rectangle -/
section
/-!
# A rectangle with uniformly bounded edges

The rectangle lemma uses only the Polish topological additive group structure
of the source. The subgroup is represented here by an arbitrary set: the proof
only needs the membership of each branch vector and the reduction identity.
This makes the result apply directly to the real linear subspaces in the paper.
-/

open Set Filter Topology TopologicalSpace

namespace NoUniversalFSigma

universe u v w

/-- A continuously varying translation in the first factor is a homeomorphism. -/
def translationShear {B : Type u} {P : Type v}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
    [TopologicalSpace P] (j : P → B) (hj : Continuous j) :
    B × P ≃ₜ B × P where
  toFun z := (z.1 + j z.2, z.2)
  invFun z := (z.1 - j z.2, z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  continuous_toFun := (continuous_fst.add (hj.comp continuous_snd)).prodMk continuous_snd
  continuous_invFun := (continuous_fst.sub (hj.comp continuous_snd)).prodMk continuous_snd

/-- The endpoint map `(x,t) ↦ x+j(t)` is open. -/
theorem isOpenMap_fst_add {B : Type u} {P : Type v}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
    [TopologicalSpace P] {j : P → B} (hj : Continuous j) :
    IsOpenMap (fun z : B × P => z.1 + j z.2) :=
  isOpenMap_fst.comp (translationShear j hj).isOpenMap

/-- The endpoint map `(x,t) ↦ x-j(t)` is open. -/
theorem isOpenMap_fst_sub {B : Type u} {P : Type v}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
    [TopologicalSpace P] {j : P → B} (hj : Continuous j) :
    IsOpenMap (fun z : B × P => z.1 - j z.2) := by
  simpa only [sub_eq_add_neg] using isOpenMap_fst_add hj.neg

/-- Lemma 4.2. The two endpoint implications require only their displayed
endpoints to belong to the set on which the map is continuous. -/
theorem rectangle_with_uniformly_bounded_edges
    {B : Type u} {P : Type v} {Y : Type w}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] [PolishSpace B]
    [TopologicalSpace P] [PolishSpace P] [Nonempty P]
    [TopologicalSpace Y] (H : Set B) (F : Y → Y → Prop)
    (j : P → B) (hj : Continuous j) (hjH : ∀ t, j t ∈ H)
    (f : B → Y) (hred : ∀ x y, (x - y ∈ H) ↔ F (f x) (f y))
    (L : ℕ → Set (Y × Y)) (hL : ∀ n, IsClosed (L n))
    (hmono : Monotone L) (hcover : ∀ a b, F a b → ∃ n, (a, b) ∈ L n)
    (C : Set B) (hC : IsGδ C) (hm : IsMeagre Cᶜ)
    (hfC : Continuous (fun x : C => f x)) :
    ∃ (n : ℕ) (V : Set B) (O : Set P),
      1 ≤ n ∧ IsOpen V ∧ IsOpen O ∧ V.Nonempty ∧ O.Nonempty ∧
        (∀ x ∈ V, ∀ t ∈ O, x ∈ C → x + j t ∈ C →
          (f (x + j t), f x) ∈ L n) ∧
        (∀ x ∈ V, ∀ t ∈ O, x ∈ C → x - j t ∈ C →
          (f x, f (x - j t)) ∈ L n) := by
  let p₀ : B × P → B := Prod.fst
  let pplus : B × P → B := fun z => z.1 + j z.2
  let pminus : B × P → B := fun z => z.1 - j z.2
  have hp₀ : Continuous p₀ := continuous_fst
  have hpplus : Continuous pplus := continuous_fst.add (hj.comp continuous_snd)
  have hpminus : Continuous pminus := continuous_fst.sub (hj.comp continuous_snd)
  let D : Set (B × P) := (p₀ ⁻¹' C) ∩ (pplus ⁻¹' C) ∩ (pminus ⁻¹' C)
  have hD : IsGδ D :=
    ((isGδ_induced hp₀ hC).inter (isGδ_induced hpplus hC)).inter (isGδ_induced hpminus hC)
  have hmD : IsMeagre Dᶜ := by
    have h₀ : (p₀ ⁻¹' C) ∈ residual (B × P) := by
      simpa only [IsMeagre, preimage_compl, compl_compl] using
        hm.preimage_of_isOpenMap hp₀ isOpenMap_fst
    have hplus : (pplus ⁻¹' C) ∈ residual (B × P) := by
      simpa only [IsMeagre, preimage_compl, compl_compl] using
        hm.preimage_of_isOpenMap hpplus (isOpenMap_fst_add hj)
    have hminus : (pminus ⁻¹' C) ∈ residual (B × P) := by
      simpa only [IsMeagre, preimage_compl, compl_compl] using
        hm.preimage_of_isOpenMap hpminus (isOpenMap_fst_sub hj)
    simpa only [IsMeagre, compl_compl] using inter_mem (inter_mem h₀ hplus) hminus
  have hd : Dense D := dense_of_mem_residual (by
    simpa only [IsMeagre, compl_compl] using hmD)
  let e₀ : D → C := fun z => ⟨p₀ z, z.property.1.1⟩
  let eplus : D → C := fun z => ⟨pplus z, z.property.1.2⟩
  let eminus : D → C := fun z => ⟨pminus z, z.property.2⟩
  have he₀ : Continuous e₀ := (hp₀.comp continuous_subtype_val).subtype_mk _
  have heplus : Continuous eplus := (hpplus.comp continuous_subtype_val).subtype_mk _
  have heminus : Continuous eminus := (hpminus.comp continuous_subtype_val).subtype_mk _
  let gplus : D → Y × Y := fun z => (f (pplus z), f (p₀ z))
  let gminus : D → Y × Y := fun z => (f (p₀ z), f (pminus z))
  have hgplus : Continuous gplus := (hfC.comp heplus).prodMk (hfC.comp he₀)
  have hgminus : Continuous gminus := (hfC.comp he₀).prodMk (hfC.comp heminus)
  let A : ℕ → Set D := fun n => (gplus ⁻¹' L n) ∩ (gminus ⁻¹' L n)
  have hA : ∀ n, IsClosed (A n) := fun n =>
    ((hL n).preimage hgplus).inter ((hL n).preimage hgminus)
  have hAcov : ⋃ n, A n = univ := by
    apply eq_univ_of_forall
    intro z
    have hplus : F (f (pplus z)) (f (p₀ z)) :=
      (hred _ _).mp (by simpa [pplus, p₀] using hjH z.val.2)
    have hminus : F (f (p₀ z)) (f (pminus z)) :=
      (hred _ _).mp (by simpa [pminus, p₀] using hjH z.val.2)
    obtain ⟨n, hn⟩ := hcover _ _ hplus
    obtain ⟨m, hm'⟩ := hcover _ _ hminus
    exact mem_iUnion.mpr ⟨max n m, hmono (le_max_left n m) hn,
      hmono (le_max_right n m) hm'⟩
  obtain ⟨n, V, O, hVo, hOo, hVne, hOne, hrect⟩ :=
    exists_open_rectangle_of_closed_cover hD hd A hA hAcov
  let Splus : Set (B × P) := (p₀ ⁻¹' C) ∩ (pplus ⁻¹' C)
  let Sminus : Set (B × P) := (p₀ ⁻¹' C) ∩ (pminus ⁻¹' C)
  let Gplus : Splus → Y × Y := fun z => (f (pplus z), f (p₀ z))
  let Gminus : Sminus → Y × Y := fun z => (f (p₀ z), f (pminus z))
  have hGplus : Continuous Gplus := by
    have he₁ : Continuous (fun z : Splus => (⟨pplus z, z.property.2⟩ : C)) :=
      (hpplus.comp continuous_subtype_val).subtype_mk _
    have he₂ : Continuous (fun z : Splus => (⟨p₀ z, z.property.1⟩ : C)) :=
      (hp₀.comp continuous_subtype_val).subtype_mk _
    exact (hfC.comp he₁).prodMk (hfC.comp he₂)
  have hGminus : Continuous Gminus := by
    have he₁ : Continuous (fun z : Sminus => (⟨p₀ z, z.property.1⟩ : C)) :=
      (hp₀.comp continuous_subtype_val).subtype_mk _
    have he₂ : Continuous (fun z : Sminus => (⟨pminus z, z.property.2⟩ : C)) :=
      (hpminus.comp continuous_subtype_val).subtype_mk _
    exact (hfC.comp he₁).prodMk (hfC.comp he₂)
  have hplus_all : ∀ z : Splus, (z : B × P) ∈ V ×ˢ O → Gplus z ∈ L n := by
    apply closed_condition_of_dense_on_open
      (show D ⊆ Splus from fun _ hz => hz.1) hd (hVo.prod hOo) hGplus (hL n)
    intro z hz
    exact (hrect ⟨z, hz.1⟩ hz.2).1
  have hminus_all : ∀ z : Sminus, (z : B × P) ∈ V ×ˢ O → Gminus z ∈ L n := by
    apply closed_condition_of_dense_on_open
      (show D ⊆ Sminus from fun _ hz => ⟨hz.1.1, hz.2⟩) hd (hVo.prod hOo) hGminus (hL n)
    intro z hz
    exact (hrect ⟨z, hz.1⟩ hz.2).2
  refine ⟨n + 1, V, O, Nat.le_add_left 1 n, hVo, hOo, hVne, hOne, ?_, ?_⟩
  · intro x hx t ht hxC hxjC
    exact hmono (Nat.le_succ n) (hplus_all ⟨(x, t), hxC, hxjC⟩ ⟨hx, ht⟩)
  · intro x hx t ht hxC hxjC
    exact hmono (Nat.le_succ n) (hminus_all ⟨(x, t), hxC, hxjC⟩ ⟨hx, ht⟩)

end NoUniversalFSigma

end

/- Source module: NoUniversalFSigma.Comparison -/
section
open Set Filter Topology TopologicalSpace

namespace NoUniversalFSigma

universe u v w

/-- Relative continuity of the reduction gives simultaneous neighborhoods for
the three moving source points, with the first point held fixed. -/
theorem three_endpoint_window
    {B : Type u} {P : Type v} {Y : Type w}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
    [TopologicalSpace P] [TopologicalSpace Y]
    (j : P → B) (hj : Continuous j) (f : B → Y) (C : Set B)
    (hfC : Continuous (fun a : C => f a))
    {V : Set B} (hV : IsOpen V) {O : Set P} (hO : IsOpen O)
    {x : B} {t r : P} (hxV : x ∈ V) (htO : t ∈ O) (hrO : r ∈ O)
    (hxplus : x + j t ∈ C) (hx : x ∈ C) (hxminus : x - j r ∈ C)
    {W : Set (Y × Y × Y)} (hW : IsOpen W)
    (hpW : (f (x + j t), f x, f (x - j r)) ∈ W) :
    ∃ (A : Set B) (U₁ U₂ : Set P),
      IsOpen A ∧ IsOpen U₁ ∧ IsOpen U₂ ∧
      x + j t ∈ A ∧ t ∈ U₁ ∧ r ∈ U₂ ∧ U₁ ⊆ O ∧ U₂ ⊆ O ∧
      ∀ v ∈ A, ∀ s ∈ U₁, ∀ q ∈ U₂,
        v - j s ∈ V ∧
        (v ∈ C → v - j s ∈ C → v - j s - j q ∈ C →
          (f v, f (v - j s), f (v - j s - j q)) ∈ W) := by
  let a : B × P × P → B := fun z => z.1
  let b : B × P × P → B := fun z => z.1 - j z.2.1
  let c : B × P × P → B := fun z => z.1 - j z.2.1 - j z.2.2
  have ha : Continuous a := continuous_fst
  have hb : Continuous b := continuous_fst.sub (hj.comp (continuous_fst.comp continuous_snd))
  have hc : Continuous c := hb.sub (hj.comp (continuous_snd.comp continuous_snd))
  let S : Set (B × P × P) := {z | a z ∈ C ∧ b z ∈ C ∧ c z ∈ C}
  let g : S → Y × Y × Y := fun z => (f (a z), f (b z), f (c z))
  have hg : Continuous g := by
    have h₁ : Continuous (fun z : S => (⟨a z, z.property.1⟩ : C)) :=
      (ha.comp continuous_subtype_val).subtype_mk _
    have h₂ : Continuous (fun z : S => (⟨b z, z.property.2.1⟩ : C)) :=
      (hb.comp continuous_subtype_val).subtype_mk _
    have h₃ : Continuous (fun z : S => (⟨c z, z.property.2.2⟩ : C)) :=
      (hc.comp continuous_subtype_val).subtype_mk _
    exact (hfC.comp h₁).prodMk ((hfC.comp h₂).prodMk (hfC.comp h₃))
  obtain ⟨N, hN, hNeq⟩ := isOpen_induced_iff.mp (hW.preimage hg)
  let z₀ : B × P × P := (x + j t, t, r)
  have hz₀ : z₀ ∈ S := by simpa [S, a, b, c, z₀] using And.intro hxplus ⟨hx, hxminus⟩
  have hzN : z₀ ∈ N := by
    have hgz : g ⟨z₀, hz₀⟩ ∈ W := by simpa [g, a, b, c, z₀] using hpW
    change (⟨z₀, hz₀⟩ : S) ∈ (Subtype.val : S → B × P × P) ⁻¹' N
    rw [hNeq]
    exact hgz
  let M : Set (B × P × P) := N ∩ (b ⁻¹' V) ∩
    ((fun z : B × P × P => z.2.1) ⁻¹' O) ∩
    ((fun z : B × P × P => z.2.2) ⁻¹' O)
  have hM : IsOpen M :=
    ((hN.inter (hV.preimage hb)).inter
      (hO.preimage (continuous_fst.comp continuous_snd))).inter
      (hO.preimage (continuous_snd.comp continuous_snd))
  have hzM : z₀ ∈ M := by
    exact ⟨⟨⟨hzN, by simpa [b, z₀] using hxV⟩, htO⟩, hrO⟩
  obtain ⟨A, U, hA, hU, hxA, htrU, hAU⟩ :=
    isOpen_prod_iff.mp hM z₀.1 z₀.2 hzM
  obtain ⟨U₁, U₂, hU₁, hU₂, htU₁, hrU₂, hUU⟩ :=
    isOpen_prod_iff.mp hU t r htrU
  have hfull {v s q} (hv : v ∈ A) (hs : s ∈ U₁) (hq : q ∈ U₂) :
      (v, s, q) ∈ M := hAU ⟨hv, hUU ⟨hs, hq⟩⟩
  refine ⟨A, U₁, U₂, hA, hU₁, hU₂, hxA, htU₁, hrU₂, ?_, ?_, ?_⟩
  · intro s hs
    exact (hfull hxA hs hrU₂).1.2
  · intro q hq
    exact (hfull hxA htU₁ hq).2
  · intro v hv s hs q hq
    have hvm := hfull hv hs hq
    refine ⟨hvm.1.1.2, ?_⟩
    intro hvC hvsC hvsqC
    have hzS : (v, s, q) ∈ S := ⟨hvC, hvsC, hvsqC⟩
    have hzN' : (⟨(v, s, q), hzS⟩ : S) ∈
        (Subtype.val : S → B × P × P) ⁻¹' N := hvm.1.1.1
    rw [hNeq] at hzN'
    exact hzN'

/-- The successor step of Proposition 4.3. A single first endpoint is chosen
after the escaping sequence is fixed, so only countably many translates of the
comeager continuity set are intersected. -/
theorem comparison_successor_step
    {B : Type u} {P : Type v} {Y : Type w}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] [PolishSpace B]
    [TopologicalSpace P] [TopologicalSpace Y]
    (H : Set B) (F : Y → Y → Prop) (j : P → B) (hj : Continuous j)
    (f : B → Y) (hred : ∀ x y, (x - y ∈ H) ↔ F (f x) (f y))
    (L : ℕ → Set (Y × Y)) (hL : ∀ n, IsClosed (L n))
    (hLF : ∀ n, L n ⊆ {p | F p.1 p.2}) (n : ℕ)
    (C : Set B) (hm : IsMeagre Cᶜ) (hfC : Continuous (fun a : C => f a))
    (V : Set B) (hV : IsOpen V) (O : Set P) (hO : IsOpen O)
    (R : Set (P × P)) (T : Set (targetTripleSet L n))
    (hcomp : ∀ t r, (t, r) ∈ R → t ∈ O → r ∈ O →
      ∀ x ∈ V, x + j t ∈ C → x ∈ C → x - j r ∈ C →
        (f (x + j t), f x, f (x - j r)) ∈ Subtype.val '' T)
    {t r : P} (htr : (t, r) ∈ escapeDerivative H j R)
    (htO : t ∈ O) (hrO : r ∈ O) {x : B} (hxV : x ∈ V)
    (hxplus : x + j t ∈ C) (hx : x ∈ C) (hxminus : x - j r ∈ C) :
    (f (x + j t), f x, f (x - j r)) ∈
      Subtype.val '' targetDerivative L n T := by
  classical
  obtain ⟨p, hpT, hpval⟩ := hcomp t r htr.1 htO hrO x hxV hxplus hx hxminus
  refine ⟨p, (mem_coverDerivative_iff (targetLevelSet L n) T p).mpr ?_, hpval⟩
  refine ⟨hpT, ?_⟩
  intro k W hW hpW
  by_contra hbad
  have hbnd : ∀ q ∈ T, q ∈ W → q ∈ targetLevelSet L n k := by
    intro q hqT hqW
    by_contra hqk
    exact hbad ⟨q, hqW, hqT, hqk⟩
  obtain ⟨W', hW', hWeq⟩ := isOpen_induced_iff.mp hW
  have hpW' : (f (x + j t), f x, f (x - j r)) ∈ W' := by
    rw [← hpval]
    change p ∈ (Subtype.val : targetTripleSet L n → Y × Y × Y) ⁻¹' W'
    rw [hWeq]
    exact hpW
  obtain ⟨A, U₁, U₂, hA, hU₁, hU₂, hxA, htU₁, hrU₂, hU₁O, hU₂O, hwindow⟩ :=
    three_endpoint_window j hj f C hfC hV hO hxV htO hrO hxplus hx hxminus hW' hpW'
  have hescape := htr.2 (U₁ ×ˢ U₂) (hU₁.prod hU₂) ⟨htU₁, hrU₂⟩
  obtain ⟨z, hz, hzH⟩ := Set.not_subset.mp hescape
  obtain ⟨b, hbmem, hbtend⟩ := mem_closure_iff_seq_limit.mp hz
  choose a ha hasum using hbmem
  have hsum : Tendsto (fun l => j (a l).1 + j (a l).2) atTop (𝓝 z) := by
    have heq : (fun l => pairSum j (a l)) = b := funext hasum
    change Tendsto (fun l => pairSum j (a l)) atTop (𝓝 z)
    rw [heq]
    exact hbtend
  let shifts : (Unit ⊕ Unit) ⊕ (ℕ ⊕ ℕ) → B
    | .inl (.inl _) => 0
    | .inl (.inr _) => z
    | .inr (.inl l) => j (a l).1
    | .inr (.inr l) => j (a l).1 + j (a l).2
  obtain ⟨v, hvA, hvall⟩ :=
    exists_mem_open_with_countably_many_translates hm hA ⟨_, hxA⟩ shifts
  have hvC : v ∈ C := by simpa [shifts] using hvall (.inl (.inl ()))
  have hvzC : v - z ∈ C := hvall (.inl (.inr ()))
  have hvmid (l : ℕ) : v - j (a l).1 ∈ C := hvall (.inr (.inl l))
  have hvlast (l : ℕ) : v - (j (a l).1 + j (a l).2) ∈ C := hvall (.inr (.inr l))
  have hlevel (l : ℕ) : (f v, f (v - (j (a l).1 + j (a l).2))) ∈ L k := by
    have hloc := hwindow v hvA (a l).1 (ha l).2.1 (a l).2 (ha l).2.2
    have hvlast' : v - j (a l).1 - j (a l).2 ∈ C := by
      simpa only [sub_sub] using hvlast l
    obtain ⟨q, hqT, hqval⟩ := hcomp (a l).1 (a l).2 (ha l).1
      (hU₁O (ha l).2.1) (hU₂O (ha l).2.2)
      (v - j (a l).1) hloc.1 (by simpa using hvC) (hvmid l) hvlast'
    have hqW : q ∈ W := by
      rw [← hWeq]
      change q.val ∈ W'
      rw [hqval]
      simpa only [sub_add_cancel] using hloc.2 hvC (hvmid l) hvlast'
    have hqk := hbnd q hqT hqW
    change (q.val.1, q.val.2.2) ∈ L k at hqk
    rw [hqval] at hqk
    simpa only [sub_add_cancel, sub_sub] using hqk
  have hvlim : Tendsto (fun l => v - (j (a l).1 + j (a l).2)) atTop (𝓝 (v - z)) :=
    tendsto_const_nhds.sub hsum
  have hvlimC : Tendsto
      (fun l => (⟨v - (j (a l).1 + j (a l).2), hvlast l⟩ : C)) atTop
      (𝓝 (⟨v - z, hvzC⟩ : C)) := tendsto_subtype_rng.mpr hvlim
  have hflim := (hfC.tendsto (⟨v - z, hvzC⟩ : C)).comp hvlimC
  have hpairs : Tendsto (fun l => (f v, f (v - (j (a l).1 + j (a l).2)))) atTop
      (𝓝 (f v, f (v - z))) := by
    rw [nhds_prod_eq]
    exact tendsto_const_nhds.prodMk hflim
  have hfinal : (f v, f (v - z)) ∈ L k :=
    (hL k).mem_of_tendsto hpairs (Eventually.of_forall hlevel)
  have hzmem : z ∈ H := by
    simpa using (hred v (v - z)).mpr (hLF k hfinal)
  exact hzH hzmem

/-- Proposition 4.3. Every escape remainder maps into the corresponding
composition remainder. Small source ordinals are lifted to the universe of the
target; in particular the target Polish space need not live in `Type 0`. -/
theorem comparison_of_derivatives
    {B : Type u} {P : Type} {Y : Type w}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] [PolishSpace B]
    [TopologicalSpace P] [TopologicalSpace Y]
    (H : Set B) (F : Y → Y → Prop) (j : P → B) (hj : Continuous j)
    (f : B → Y) (hred : ∀ x y, (x - y ∈ H) ↔ F (f x) (f y))
    (L : ℕ → Set (Y × Y)) (hL : ∀ n, IsClosed (L n))
    (hLF : ∀ n, L n ⊆ {p | F p.1 p.2}) (n : ℕ)
    (C : Set B) (hm : IsMeagre Cᶜ) (hfC : Continuous (fun a : C => f a))
    (V : Set B) (hV : IsOpen V) (O : Set P) (hO : IsOpen O)
    (hplus : ∀ x ∈ V, ∀ t ∈ O, x ∈ C → x + j t ∈ C → (f (x + j t), f x) ∈ L n)
    (hminus : ∀ x ∈ V, ∀ t ∈ O, x ∈ C → x - j t ∈ C → (f x, f (x - j t)) ∈ L n)
    (ξ : Ordinal.{0}) :
    ∀ t r, (t, r) ∈ escapeRemainder H j ξ → t ∈ O → r ∈ O →
      ∀ x ∈ V, x + j t ∈ C → x ∈ C → x - j r ∈ C →
        (f (x + j t), f x, f (x - j r)) ∈
          Subtype.val '' targetIter L n (Ordinal.lift.{w} ξ) := by
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
    intro t r htr htO hrO x hxV hxplus hx hxminus
    have hbase : (f (x + j t), f x, f (x - j r)) ∈ targetTripleSet L n :=
      ⟨hplus x hxV t htO hx hxplus, hminus x hxV r hrO hx hxminus⟩
    let p : targetTripleSet L n := ⟨(f (x + j t), f x, f (x - j r)), hbase⟩
    refine ⟨p, ?_, rfl⟩
    change p ∈ OrdinalApprox.gfpApprox (targetDerivative L n) univ (Ordinal.lift.{w} ξ)
    rw [OrdinalApprox.gfpApprox]
    refine ⟨mem_univ _, mem_iInter.mpr fun η => mem_iInter.mpr fun hη => ?_⟩
    obtain ⟨δ, rfl⟩ := Ordinal.mem_range_lift_of_le hη.le
    have hδ : δ < ξ := Ordinal.lift_lt.mp hη
    have hsource : (t, r) ∈ escapeDerivative H j (escapeRemainder H j δ) := by
      change (t, r) ∈ OrdinalApprox.gfpApprox (escapeOperator H j) univ ξ at htr
      rw [OrdinalApprox.gfpApprox] at htr
      exact mem_iInter.mp (mem_iInter.mp htr.2 δ) hδ
    obtain ⟨q, hq, hqval⟩ := comparison_successor_step H F j hj f hred L hL hLF n
      C hm hfC V hV O hO (escapeRemainder H j δ)
      (targetIter L n (Ordinal.lift.{w} δ)) (IH δ hδ)
      hsource htO hrO hxV hxplus hx hxminus
    have hqp : q = p := Subtype.ext hqval
    exact hqp ▸ hq

/-- Corollary 4.4: if all source diagonal pairs survive a given stage, then
some target composition remainder at that stage is nonempty. -/
theorem rank_obstruction
    {B : Type u} {P : Type} {Y : Type w}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] [PolishSpace B]
    [TopologicalSpace P] [PolishSpace P] [Nonempty P]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    (H : Set B) (F : Y → Y → Prop) (j : P → B) (hj : Continuous j)
    (hjH : ∀ t, j t ∈ H)
    (f : B → Y) (hf : IsBaireMeasurable f)
    (hred : ∀ x y, (x - y ∈ H) ↔ F (f x) (f y))
    (L : ℕ → Set (Y × Y)) (hL : ∀ n, IsClosed (L n))
    (hmono : Monotone L) (hLF : ∀ n, L n ⊆ {p | F p.1 p.2})
    (hcover : ∀ a b, F a b → ∃ n, (a, b) ∈ L n)
    (ξ : Ordinal.{0}) (hdiag : ∀ t, (t, t) ∈ escapeRemainder H j ξ) :
    ∃ n, (targetIter L n (Ordinal.lift.{w} ξ)).Nonempty := by
  obtain ⟨C, hC, hm, hfC⟩ := baire_measurable_continuous_on_comeagre_gdelta f hf
  obtain ⟨n, V, O, _, hV, hO, hVne, hOne, hplus, hminus⟩ :=
    rectangle_with_uniformly_bounded_edges H F j hj hjH f hred L hL hmono hcover C hC hm hfC
  obtain ⟨t, htO⟩ := hOne
  let shifts : Option Bool → B
    | none => 0
    | some false => -j t
    | some true => j t
  obtain ⟨x, hxV, hxall⟩ :=
    exists_mem_open_with_countably_many_translates hm hV hVne shifts
  have hx : x ∈ C := by simpa [shifts] using hxall none
  have hxplus : x + j t ∈ C := by simpa [shifts] using hxall (some false)
  have hxminus : x - j t ∈ C := hxall (some true)
  obtain ⟨p, hp, _⟩ := comparison_of_derivatives H F j hj f hred L hL hLF n C hm hfC
    V hV O hO hplus hminus ξ t t (hdiag t) htO htO x hxV hxplus hx hxminus
  exact ⟨n, p, hp⟩

/-- A target rank bound and a surviving source diagonal rule out every
Baire-measurable reduction of the associated coset relation to the target. -/
theorem not_baire_reducible_of_diagonal_escape
    {B : Type u} {P : Type} {Y : Type w}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B] [PolishSpace B]
    [TopologicalSpace P] [PolishSpace P] [Nonempty P]
    [TopologicalSpace Y] [SecondCountableTopology Y]
    (H : Set B) (F : Y → Y → Prop) (j : P → B) (hj : Continuous j)
    (hjH : ∀ t, j t ∈ H)
    (L : ℕ → Set (Y × Y)) (hL : ∀ n, IsClosed (L n))
    (hmono : Monotone L) (hLF : ∀ n, L n ⊆ {p | F p.1 p.2})
    (hcover : ∀ a b, F a b → ∃ n, (a, b) ∈ L n)
    (ξ : Ordinal.{0}) (hdiag : ∀ t, (t, t) ∈ escapeRemainder H j ξ)
    (hempty : ∀ n, targetIter L n (Ordinal.lift.{w} ξ) = ∅) :
    ¬ ∃ f : B → Y, IsBaireMeasurable f ∧
      ∀ x y, (x - y ∈ H) ↔ F (f x) (f y) := by
  rintro ⟨f, hf, hred⟩
  obtain ⟨n, p, hp⟩ := rank_obstruction H F j hj hjH f hf hred L hL hmono hLF hcover ξ hdiag
  simpa only [hempty n, mem_empty_iff_false] using hp

end NoUniversalFSigma

end

/- Source module: NoUniversalFSigma.MainReduction -/
section
/-!
# Final rank obstruction reduction

This module isolates the final deduction of Theorem 1.1 from the existence of
admissible families of every countable diagonal rank. The remaining construction
obligation is explicit in the hypothesis of `main_of_rankWitnesses`.
-/

noncomputable section

open Set TopologicalSpace
open scoped Ordinal

namespace NoUniversalFSigma

universe u

/-- The final deduction in Theorem 1.1, conditional on the countable-rank
family construction. This conditional theorem is not the completed main theorem. -/
theorem main_of_rankWitnesses
    (hWitness : ∀ α : Ordinal.{0}, α < ω₁ →
      ∃ A : AdmissibleFamily, HasDiagonalRank A α)
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : IsFSigmaRelation F.r) :
    ∃ H : Submodule ℝ RealL2,
      IsFSigma (H : Set RealL2) ∧
      IsFSigmaRelation (CosetRelation H) ∧
      ¬ ∃ f : RealL2 → Y,
        IsBaireMeasurable f ∧ IsReduction f (CosetRelation H) F.r := by
  let C : ClosedRelationCover F := Classical.choice (exists_closedRelationCover F hF)
  obtain ⟨α, hα, hempty⟩ := targetIter_exists_uniform_countable_empty_lift
    F.r F.iseqv C.level C.isClosed_level C.iUnion_eq
  obtain ⟨A, hA⟩ := hWitness α hα
  refine ⟨A.span, A.isFSigma_span, isFSigma_cosetRelation A.span A.isFSigma_span, ?_⟩
  exact not_baire_reducible_of_diagonal_escape (A.span : Set RealL2) F.r
    A.j A.continuous_j A.j_mem_span
    C.level C.isClosed_level C.monotone_level
    (fun n p hp => C.subset_relation n p hp) C.covers α hA hempty

/-- The same rank witnesses rule out a universal `Fσ` equivalence relation
under Borel reducibility. -/
theorem not_universal_of_rankWitnesses
    (hWitness : ∀ α : Ordinal.{0}, α < ω₁ →
      ∃ A : AdmissibleFamily, HasDiagonalRank A α)
    {Y : Type} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : IsFSigmaRelation F.r) : ¬ IsUniversalFSigma F.r := by
  intro hUniversal
  obtain ⟨H, _, hCoset, hnon⟩ := main_of_rankWitnesses hWitness F hF
  obtain ⟨f, hf, hred⟩ := hUniversal RealL2 (CosetRelation H)
    (cosetRelation_equivalence H) hCoset
  exact hnon ⟨f, isBorelMeasurable_isBaireMeasurable hf, hred⟩

end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.RankConstruction -/
section
/-! Transfinite assembly. The sole certificate parameter is precisely the
algebraic-span conclusion of the countable closed-chart construction. -/

noncomputable section
open Set
open scoped Ordinal

namespace NoUniversalFSigma

/-- Assemble actual rank witnesses once the countable tensor spans have their
closed-chart certificates. The parameter is explicit, and this is an
infrastructure lemma rather than the final theorem. -/
theorem rankWitnesses_of_tensorFSigma
    (hTensor : ∀ A : ℕ → AdmissibleFamily,
      IsFSigma (Submodule.span ℝ (range (TensorFamily.family A)) : Set TensorFamily.Fock)) :
    ∀ α : Ordinal.{0}, α < ω₁ → ∃ A : AdmissibleFamily, HasDiagonalRank A α := by
  apply countableOrdinal_induction
  · exact ⟨baseFamily, HilbertFamily.hasDiagonalRank_zero baseFamily⟩
  · intro α _ hα
    obtain ⟨A, hA⟩ := hα
    exact ⟨successorFamily A, successorFamily_hasDiagonalRank A α hA⟩
  · intro ζ _ hζ a _ hcofinal hA
    choose A hA using hA
    exact ⟨limitFamily A (hTensor A),
      limitFamily_hasDiagonalRank_limit A (hTensor A) a hζ hcofinal hA⟩

end NoUniversalFSigma
end
end

/- Source module: NoUniversalFSigma.FiniteTensor -/
section
noncomputable section

open Set Matrix
open scoped BigOperators

namespace NoUniversalFSigma
namespace FiniteTensor

/-- Finitely many independent coordinate vectors admit a nonsingular coordinate
minor. The coordinate index type itself can be infinite. -/
theorem exists_coordinate_pivot {I : Type*} {r : ℕ} (f : Fin r → I → ℝ)
    (hf : LinearIndependent ℝ f) :
    ∃ rows : Fin r → I, Matrix.det (fun i j => f j (rows i)) ≠ 0 := by
  have htop : Submodule.span ℝ (range (Function.swap f)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hf
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (Function.swap f)
  let b : Module.Basis κ ℝ (Fin r → ℝ) := Module.Basis.mk hli (by rw [hspan, htop])
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card κ = r := by
    rw [← Module.finrank_eq_card_basis b]
    simp
  let e : Fin r ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  refine ⟨a ∘ e, ?_⟩
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hli.comp e e.injective

end FiniteTensor
end NoUniversalFSigma


namespace NoUniversalFSigma.FiniteTensor

/-- The algebraic column space of an infinite real matrix. -/
def columnSpace {I J : Type*} (A : I → J → ℝ) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ (range (fun j i => A i j))

/-- Finite-dimensional column spaces have a basis consisting of actual columns. -/
theorem exists_column_basis {I J : Type*} (A : I → J → ℝ)
    [FiniteDimensional ℝ (columnSpace A)] :
    ∃ r : ℕ, ∃ cols : Fin r → J,
      LinearIndependent ℝ (fun t i => A i (cols t)) ∧
      Submodule.span ℝ (range (fun t i => A i (cols t))) = columnSpace A := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℝ (fun j i => A i j)
  have hspan' : Submodule.span ℝ (range ((fun j i => A i j) ∘ a)) = columnSpace A := hspan
  letI : FiniteDimensional ℝ (Submodule.span ℝ (range ((fun j i => A i j) ∘ a))) :=
    hspan'.symm ▸ inferInstance
  letI : Fintype κ := FiniteDimensional.fintypeBasisIndex (Module.Basis.span hli)
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, hli.comp e e.injective, ?_⟩
  have hrange : range (fun t i => A i ((a ∘ e) t)) =
      range ((fun j i => A i j) ∘ a) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩; exact ⟨e t, rfl⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨t, rfl⟩ := e.surjective k
      exact ⟨t, rfl⟩
  rw [hrange]
  exact hspan'

/-- A nonsingular pivot reconstructs every column once the selected columns span
all the columns. The adjugate form makes reconstruction polynomial. -/
theorem pivot_reconstruction {I J : Type*} {r : ℕ}
    (A : I → J → ℝ) (cols : Fin r → J) (rows : Fin r → I)
    (hspan : ∀ j, (fun i => A i j) ∈
      Submodule.span ℝ (range (fun t i => A i (cols t)))) (i : I) (j : J) :
    Matrix.det (fun s t => A (rows s) (cols t)) * A i j =
      (fun t => A i (cols t)) ⬝ᵥ
        ((Matrix.adjugate (fun s t => A (rows s) (cols t))) *ᵥ (fun s => A (rows s) j)) := by
  classical
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hspan j)
  have heq (a : I) : ∑ t, c t * A a (cols t) = A a j := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc a
  have hvec : (fun s => A (rows s) j) =
      (fun s t => A (rows s) (cols t)) *ᵥ c := by
    funext s
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using (heq (rows s)).symm
  rw [hvec, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul]
  congr 1
  simpa only [dotProduct, mul_comm] using (heq i).symm

/-- Every finite-rank coordinate matrix has a nonsingular finite pivot and an
exact polynomial row-column reconstruction. -/
theorem exists_finite_pivot {I J : Type*} (A : I → J → ℝ)
    [FiniteDimensional ℝ (columnSpace A)] :
    ∃ r : ℕ, ∃ cols : Fin r → J, ∃ rows : Fin r → I,
      Matrix.det (fun s t => A (rows s) (cols t)) ≠ 0 ∧
      ∀ i j, Matrix.det (fun s t => A (rows s) (cols t)) * A i j =
        (fun t => A i (cols t)) ⬝ᵥ
          (Matrix.adjugate (fun s t => A (rows s) (cols t)) *ᵥ (fun s => A (rows s) j)) := by
  obtain ⟨r, cols, hli, hspan⟩ := exists_column_basis A
  obtain ⟨rows, hdet⟩ := exists_coordinate_pivot (fun t i => A i (cols t)) hli
  refine ⟨r, cols, rows, hdet, pivot_reconstruction A cols rows ?_⟩
  intro j
  rw [hspan]
  exact Submodule.subset_span (mem_range_self j)

end NoUniversalFSigma.FiniteTensor


namespace NoUniversalFSigma.FiniteTensor

@[simp] theorem columnSpace_zero {I J : Type*} :
    columnSpace (fun (_ : I) (_ : J) => (0 : ℝ)) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact Submodule.zero_mem _

theorem columnSpace_add_le {I J : Type*} (A B : I → J → ℝ) :
    columnSpace (fun i j => A i j + B i j) ≤ columnSpace A ⊔ columnSpace B := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (columnSpace A ⊔ columnSpace B).add_mem
    (Submodule.mem_sup_left (Submodule.subset_span (mem_range_self j)))
    (Submodule.mem_sup_right (Submodule.subset_span (mem_range_self j)))

theorem columnSpace_smul_le {I J : Type*} (c : ℝ) (A : I → J → ℝ) :
    columnSpace (fun i j => c * A i j) ≤ columnSpace A := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact (columnSpace A).smul_mem c (Submodule.subset_span (mem_range_self j))

end NoUniversalFSigma.FiniteTensor






namespace NoUniversalFSigma.FiniteTensor
open L2Coordinates

variable {I J : Type*}

/-- The algebraic tensor product of two subspaces in the coordinate Hilbert
matrix space. No topological closure is taken. -/
def algebraicProduct (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J)) :
    Submodule ℝ (MatrixL2 I J) :=
  Submodule.span ℝ (range (fun p : H × K => outer (p.1 : L2 I) (p.2 : L2 J)))

theorem outer_mem_algebraicProduct (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    {x : L2 I} {y : L2 J} (hx : x ∈ H) (hy : y ∈ K) :
    outer x y ∈ algebraicProduct H K :=
  Submodule.subset_span (mem_range_self ((⟨x, hx⟩ : H), (⟨y, hy⟩ : K)))

theorem col_mem_of_mem_algebraicProduct (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    {T : MatrixL2 I J} (hT : T ∈ algebraicProduct H K) (j : J) : col j T ∈ H := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨p, rfl⟩ := hT
    rw [col_outer]
    exact H.smul_mem _ p.1.property
  | zero => simpa using H.zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using H.add_mem IHx IHy
  | smul a x hx IH => simpa only [map_smul] using H.smul_mem a IH

theorem row_mem_of_mem_algebraicProduct (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    {T : MatrixL2 I J} (hT : T ∈ algebraicProduct H K) (i : I) : row i T ∈ K := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨p, rfl⟩ := hT
    rw [row_outer]
    exact K.smul_mem _ p.2.property
  | zero => simpa using K.zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using K.add_mem IHx IHy
  | smul a x hx IH => simpa only [map_smul] using K.smul_mem a IH

/-- Finite tensor sums have finite-dimensional algebraic column space. -/
theorem finiteDimensional_columnSpace (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    {T : MatrixL2 I J} (hT : T ∈ algebraicProduct H K) :
    FiniteDimensional ℝ (columnSpace (fun i j => T (i, j))) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨p, rfl⟩ := hT
    let W := Submodule.span ℝ ({fun i => (p.1 : L2 I) i} : Set (I → ℝ))
    have hW : columnSpace (fun i j => outer (p.1 : L2 I) (p.2 : L2 J) (i, j)) ≤ W := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have hx : (fun i => (p.1 : L2 I) i) ∈ W := Submodule.subset_span (by simp)
      convert W.smul_mem ((p.2 : L2 J) j) hx using 1
      funext i
      simp [mul_comm]
    letI : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_singleton _)
    exact Submodule.finiteDimensional_of_le hW
  | zero =>
    change FiniteDimensional ℝ (columnSpace (fun (_ : I) (_ : J) => (0 : ℝ)))
    rw [columnSpace_zero]
    infer_instance
  | add x y hx hy IHx IHy =>
    letI := IHx
    letI := IHy
    exact Submodule.finiteDimensional_of_le
      (columnSpace_add_le (fun i j => x (i, j)) (fun i j => y (i, j)))
  | smul a x hx IH =>
    letI := IH
    exact Submodule.finiteDimensional_of_le (columnSpace_smul_le a (fun i j => x (i, j)))

end NoUniversalFSigma.FiniteTensor

namespace NoUniversalFSigma.FiniteTensor
open L2Coordinates
variable {I J : Type*}

/-- A finite coordinate pivot of a Hilbert matrix. -/
def pivot {r : ℕ} (cols : Fin r → J) (rows : Fin r → I) (T : MatrixL2 I J) :
    Matrix (Fin r) (Fin r) ℝ := fun s t => T (rows s, cols t)

/-- Polynomial reconstruction from the selected columns and rows. -/
def reconstruction {r : ℕ} (cols : Fin r → J) (rows : Fin r → I)
    (T : MatrixL2 I J) : MatrixL2 I J :=
  ∑ t, ∑ s, (pivot cols rows T).adjugate t s • outer (col (cols t) T) (row (rows s) T)

theorem reconstruction_apply {r : ℕ} (cols : Fin r → J) (rows : Fin r → I)
    (T : MatrixL2 I J) (i : I) (j : J) :
    reconstruction cols rows T (i, j) =
      ∑ t, ∑ s, (pivot cols rows T).adjugate t s *
        (T (i, cols t) * T (rows s, j)) := by
  change (lp.evalCLM ℝ (fun _ : I × J => ℝ) 2 (i, j)) (reconstruction cols rows T) = _
  simp only [reconstruction, map_sum, map_smul, smul_eq_mul]
  rfl

theorem continuous_pivot {r : ℕ} (cols : Fin r → J) (rows : Fin r → I) :
    Continuous (pivot cols rows) :=
  continuous_pi fun s => continuous_pi fun t =>
    (lp.evalCLM ℝ (fun _ : I × J => ℝ) 2 (rows s, cols t)).continuous

theorem continuous_reconstruction {r : ℕ} (cols : Fin r → J) (rows : Fin r → I) :
    Continuous (reconstruction cols rows) := by
  apply continuous_finsetSum _
  intro t ht
  apply continuous_finsetSum _
  intro s hs
  apply Continuous.smul
  · exact (continuous_apply s).comp ((continuous_apply t).comp
      (continuous_pivot cols rows).matrix_adjugate)
  · exact continuous_outer.comp ((col (cols t)).continuous.prodMk (row (rows s)).continuous)

/-- Closed row-column charts for the algebraic tensor subspace. -/
def chart (HC : ℕ → Set (L2 I)) (KC : ℕ → Set (L2 J))
    {r : ℕ} (cols : Fin r → J) (rows : Fin r → I) (m : ℕ)
    (a b : Fin r → ℕ) : Set (MatrixL2 I J) :=
  {T | (1 : ℝ) / (m + 1) ≤ |(pivot cols rows T).det| ∧
    (∀ t, col (cols t) T ∈ HC (a t)) ∧
    (∀ s, row (rows s) T ∈ KC (b s)) ∧
    (pivot cols rows T).det • T = reconstruction cols rows T}

theorem isClosed_chart (HC : ℕ → Set (L2 I)) (KC : ℕ → Set (L2 J))
    (hHC : ∀ a, IsClosed (HC a)) (hKC : ∀ b, IsClosed (KC b))
    {r : ℕ} (cols : Fin r → J) (rows : Fin r → I) (m : ℕ) (a b : Fin r → ℕ) :
    IsClosed (chart HC KC cols rows m a b) := by
  apply IsClosed.inter
  · exact isClosed_le continuous_const (continuous_pivot cols rows).matrix_det.abs
  · apply IsClosed.inter
    · convert isClosed_iInter (fun t => (hHC (a t)).preimage (col (cols t)).continuous) using 1
      ext T; simp only [Set.mem_iInter, Set.mem_preimage]; rfl
    · apply IsClosed.inter
      · convert isClosed_iInter (fun s => (hKC (b s)).preimage (row (rows s)).continuous) using 1
        ext T; simp only [Set.mem_iInter, Set.mem_preimage]; rfl
      · exact isClosed_eq ((continuous_pivot cols rows).matrix_det.smul continuous_id)
          (continuous_reconstruction cols rows)

/-- Every member of a reconstruction chart belongs to the exact algebraic tensor
span. The determinant bound permits division by its nonzero scalar. -/
theorem chart_subset_algebraicProduct (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    (HC : ℕ → Set (L2 I)) (KC : ℕ → Set (L2 J))
    (hHC : ∀ a, HC a ⊆ H) (hKC : ∀ b, KC b ⊆ K)
    {r : ℕ} (cols : Fin r → J) (rows : Fin r → I) (m : ℕ) (a b : Fin r → ℕ) :
    chart HC KC cols rows m a b ⊆ algebraicProduct H K := by
  intro T hT
  have hdet : (pivot cols rows T).det ≠ 0 := by
    have hpos : (0 : ℝ) < (1 : ℝ) / (m + 1) := by positivity
    exact abs_pos.mp (hpos.trans_le hT.1)
  have hreconstruct : reconstruction cols rows T ∈ algebraicProduct H K := by
    apply Submodule.sum_mem
    intro t ht
    apply Submodule.sum_mem
    intro s hs
    exact Submodule.smul_mem _ _
      (outer_mem_algebraicProduct H K (hHC _ (hT.2.1 t)) (hKC _ (hT.2.2.1 s)))
  have hmem : (pivot cols rows T).det • T ∈ algebraicProduct H K := hT.2.2.2 ▸ hreconstruct
  exact (Submodule.smul_mem_iff _ hdet).mp hmem

end NoUniversalFSigma.FiniteTensor


namespace NoUniversalFSigma.FiniteTensor
open L2Coordinates
variable {I J : Type*}

/-- Countable data specifying one finite row-column chart. -/
def ChartData (I J : Type*) :=
  Σ r : ℕ, (Fin r → J) × (Fin r → I) × ℕ × (Fin r → ℕ) × (Fin r → ℕ)

def chartFromData (HC : ℕ → Set (L2 I)) (KC : ℕ → Set (L2 J)) :
    ChartData I J → Set (MatrixL2 I J) :=
  fun ⟨_, cols, rows, m, a, b⟩ => chart HC KC cols rows m a b

instance [Countable I] [Countable J] : Countable (ChartData I J) := by
  unfold ChartData
  infer_instance

instance : Nonempty (ChartData I J) :=
  ⟨⟨0, Fin.elim0, Fin.elim0, 0, fun _ => 0, fun _ => 0⟩⟩

theorem isClosed_chartFromData (HC : ℕ → Set (L2 I)) (KC : ℕ → Set (L2 J))
    (hHC : ∀ a, IsClosed (HC a)) (hKC : ∀ b, IsClosed (KC b)) (d : ChartData I J) :
    IsClosed (chartFromData HC KC d) := by
  obtain ⟨r, cols, rows, m, a, b⟩ := d
  exact isClosed_chart HC KC hHC hKC cols rows m a b

/-- Every finite tensor sum lies in one of the closed polynomial charts. -/
theorem exists_chart_of_mem_algebraicProduct
    (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    (HC : ℕ → Set (L2 I)) (KC : ℕ → Set (L2 J))
    (hHC : (H : Set (L2 I)) = ⋃ a, HC a)
    (hKC : (K : Set (L2 J)) = ⋃ b, KC b)
    {T : MatrixL2 I J} (hT : T ∈ algebraicProduct H K) :
    ∃ d : ChartData I J, T ∈ chartFromData HC KC d := by
  letI := finiteDimensional_columnSpace H K hT
  obtain ⟨r, cols, rows, hdet, hrec⟩ := exists_finite_pivot (fun i j => T (i, j))
  have hcols : ∀ t : Fin r, ∃ a, col (cols t) T ∈ HC a := by
    intro t
    have h := col_mem_of_mem_algebraicProduct H K hT (cols t)
    change col (cols t) T ∈ (H : Set (L2 I)) at h
    rw [hHC] at h
    exact mem_iUnion.mp h
  have hrows : ∀ s : Fin r, ∃ b, row (rows s) T ∈ KC b := by
    intro s
    have h := row_mem_of_mem_algebraicProduct H K hT (rows s)
    change row (rows s) T ∈ (K : Set (L2 J)) at h
    rw [hKC] at h
    exact mem_iUnion.mp h
  choose a ha using hcols
  choose b hb using hrows
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (abs_pos.mpr hdet)
  refine ⟨⟨r, cols, rows, m, a, b⟩, hm.le, ha, hb, ?_⟩
  ext p
  change (pivot cols rows T).det * T p = reconstruction cols rows T p
  rw [show p = (p.1, p.2) from rfl, reconstruction_apply]
  apply (hrec p.1 p.2).trans
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro s hs
  unfold pivot
  ring

/-- The finite algebraic tensor product of two F-sigma subspaces of countably
indexed real Hilbert sequence spaces is F-sigma in their Hilbert matrix space.
This is Lemma 6.1, in coordinate Hilbert form. -/
theorem isFSigma_algebraicProduct [Countable I] [Countable J]
    (H : Submodule ℝ (L2 I)) (K : Submodule ℝ (L2 J))
    (hH : IsFSigma (H : Set (L2 I))) (hK : IsFSigma (K : Set (L2 J))) :
    IsFSigma (algebraicProduct H K : Set (MatrixL2 I J)) := by
  obtain ⟨HC, hHCclosed, hHC⟩ := hH
  obtain ⟨KC, hKCclosed, hKC⟩ := hK
  have hHCsub : ∀ a, HC a ⊆ H := by
    intro a x hx
    rw [hHC]
    exact mem_iUnion.mpr ⟨a, hx⟩
  have hKCsub : ∀ b, KC b ⊆ K := by
    intro b x hx
    rw [hKC]
    exact mem_iUnion.mpr ⟨b, hx⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ChartData I J)
  refine ⟨fun n => chartFromData HC KC (e n),
    fun n => isClosed_chartFromData HC KC hHCclosed hKCclosed (e n), ?_⟩
  ext T
  constructor
  · intro hT
    obtain ⟨d, hd⟩ := exists_chart_of_mem_algebraicProduct H K HC KC hHC hKC hT
    obtain ⟨n, rfl⟩ := he d
    exact mem_iUnion.mpr ⟨n, hd⟩
  · intro hT
    obtain ⟨n, hn⟩ := mem_iUnion.mp hT
    rcases hd : e n with ⟨r, cols, rows, m, a, b⟩
    have hn' : T ∈ chart HC KC cols rows m a b := by
      simpa only [hd, chartFromData] using hn
    exact chart_subset_algebraicProduct H K HC KC hHCsub hKCsub cols rows m a b hn'

end NoUniversalFSigma.FiniteTensor

namespace NoUniversalFSigma.FiniteTensor
open L2Coordinates
variable {I J P Q : Type*}

/-- Tensoring the spans is exactly spanning all pure products of the generators. -/
theorem algebraicProduct_span_range (j : P → L2 I) (k : Q → L2 J) :
    algebraicProduct (Submodule.span ℝ (range j)) (Submodule.span ℝ (range k)) =
      Submodule.span ℝ (range (fun p : P × Q => outer (j p.1) (k p.2))) := by
  let M := Submodule.span ℝ (range (fun p : P × Q => outer (j p.1) (k p.2)))
  have hpure : ∀ x ∈ Submodule.span ℝ (range j),
      ∀ y ∈ Submodule.span ℝ (range k), outer x y ∈ M := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨q, rfl⟩ := hy
        exact Submodule.subset_span (mem_range_self (p, q))
      | zero => simpa using M.zero_mem
      | add y z hy hz IHy IHz => simpa only [outer_add_right] using M.add_mem IHy IHz
      | smul a y hy IH => simpa only [outer_smul_right] using M.smul_mem a IH
    | zero => intro y hy; simpa using M.zero_mem
    | add x z hx hz IHx IHz =>
      intro y hy
      simpa only [outer_add_left] using M.add_mem (IHx y hy) (IHz y hy)
    | smul a x hx IH =>
      intro y hy
      simpa only [outer_smul_left] using M.smul_mem a (IH y hy)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact hpure p.1 p.1.property p.2 p.2.property
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    exact outer_mem_algebraicProduct _ _ (Submodule.subset_span (mem_range_self p.1))
      (Submodule.subset_span (mem_range_self p.2))

/-- F-sigma spans of two generator families give an F-sigma span of their pure
products, including families whose parameter types are uncountable. -/
theorem isFSigma_span_outer [Countable I] [Countable J]
    (j : P → L2 I) (k : Q → L2 J)
    (hj : IsFSigma (Submodule.span ℝ (range j) : Set (L2 I)))
    (hk : IsFSigma (Submodule.span ℝ (range k) : Set (L2 J))) :
    IsFSigma (Submodule.span ℝ (range (fun p : P × Q => outer (j p.1) (k p.2))) :
      Set (MatrixL2 I J)) := by
  rw [← algebraicProduct_span_range]
  exact isFSigma_algebraicProduct _ _ hj hk

end NoUniversalFSigma.FiniteTensor
end
end

/- Source module: NoUniversalFSigma.PacketSpan -/
section
noncomputable section
open Set

namespace NoUniversalFSigma
namespace PacketSpan

variable {P B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A mass-one family with its constant coordinate adjoined. -/
def augmentedPair (β : ℝ) (j : P → B) : P → ℝ × B := fun p => (1, β • j p)

/-- The linear graph map underlying the augmented family. -/
def massGraph (ρ : B →L[ℝ] ℝ) (β : ℝ) : B →L[ℝ] ℝ × B :=
  ρ.prod (β • ContinuousLinearMap.id ℝ B)

theorem massGraph_mem_span (ρ : B →L[ℝ] ℝ) (β : ℝ) (j : P → B)
    (hmass : ∀ p, ρ (j p) = 1) {x : B}
    (hx : x ∈ Submodule.span ℝ (range j)) :
    massGraph ρ β x ∈ Submodule.span ℝ (range (augmentedPair β j)) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    have hp : massGraph ρ β (j p) = augmentedPair β j p := by
      ext <;> simp [massGraph, augmentedPair, hmass]
    rw [hp]
    exact Submodule.subset_span (mem_range_self p)
  | zero => simpa using (Submodule.span ℝ (range (augmentedPair β j))).zero_mem
  | add x y hx hy IHx IHy => simpa only [map_add] using
      (Submodule.span ℝ (range (augmentedPair β j))).add_mem IHx IHy
  | smul a x hx IH => simpa only [map_smul] using
      (Submodule.span ℝ (range (augmentedPair β j))).smul_mem a IH

/-- The augmented span is exactly a closed scalar condition over the original span. -/
theorem mem_span_augmentedPair_iff (ρ : B →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (j : P → B) (hmass : ∀ p, ρ (j p) = 1) (v : ℝ × B) :
    v ∈ Submodule.span ℝ (range (augmentedPair β j)) ↔
      v.2 ∈ Submodule.span ℝ (range j) ∧ β * v.1 = ρ v.2 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨p, rfl⟩ := hv
      exact ⟨Submodule.smul_mem _ β (Submodule.subset_span (mem_range_self p)),
        by simp [augmentedPair, hmass]⟩
    | zero => simp
    | add x y hx hy IHx IHy =>
      refine ⟨Submodule.add_mem _ IHx.1 IHy.1, ?_⟩
      change β * (x.1 + y.1) = ρ (x.2 + y.2)
      rw [map_add, mul_add, IHx.2, IHy.2]
    | smul a x hx IH =>
      refine ⟨Submodule.smul_mem _ a IH.1, ?_⟩
      change β * (a * x.1) = ρ (a • x.2)
      rw [map_smul, ← IH.2]
      change β * (a * x.1) = a * (β * x.1)
      ring
  · rintro ⟨hv, hmassv⟩
    have hx : β⁻¹ • v.2 ∈ Submodule.span ℝ (range j) := Submodule.smul_mem _ _ hv
    have hmem := massGraph_mem_span ρ β j hmass hx
    have heq : massGraph ρ β (β⁻¹ • v.2) = v := by
      ext
      · change ρ (β⁻¹ • v.2) = v.1
        simp only [map_smul, smul_eq_mul, ← hmassv]
        field_simp
      · change β • (β⁻¹ • v.2) = v.2
        simp [smul_smul, hβ]
    exact heq ▸ hmem

/-- F-sigma algebraic span is preserved by adjoining the mass coordinate. -/
theorem isFSigma_span_augmentedPair (ρ : B →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (j : P → B) (hmass : ∀ p, ρ (j p) = 1)
    (hj : IsFSigma (Submodule.span ℝ (range j) : Set B)) :
    IsFSigma (Submodule.span ℝ (range (augmentedPair β j)) : Set (ℝ × B)) := by
  have heq : (Submodule.span ℝ (range (augmentedPair β j)) : Set (ℝ × B)) =
      (Prod.snd ⁻¹' (Submodule.span ℝ (range j) : Set B)) ∩
        {v | β * v.1 = ρ v.2} := by
    ext v
    exact mem_span_augmentedPair_iff ρ β hβ j hmass v
  rw [heq]
  exact (hj.preimage continuous_snd).inter_isClosed
    (isClosed_eq (continuous_const.mul continuous_fst) (ρ.continuous.comp continuous_snd))

end PacketSpan
end NoUniversalFSigma

namespace NoUniversalFSigma.PacketSpan
open L2Coordinates

/-- Splitting off the extra mass coordinate is a linear homeomorphism. -/
def augmentEquiv : (ℝ × RealL2) ≃L[ℝ] L2 (Option ℕ) where
  toFun := FiniteL2.augmentCLM
  map_add' := map_add _
  map_smul' := map_smul _
  invFun v := (FiniteL2.head v, FiniteL2.tail v)
  left_inv p := by rcases p with ⟨a, v⟩; simp
  right_inv v := FiniteL2.augment_head_tail v
  continuous_toFun := FiniteL2.augmentCLM.continuous
  continuous_invFun := FiniteL2.head.continuous.prodMk FiniteL2.tail.continuous

/-- One augmented coordinate family has F-sigma span. -/
theorem isFSigma_span_augment {P : Type*} (j : P → RealL2)
    (ρ : RealL2 →L[ℝ] ℝ) (β : ℝ) (hβ : β ≠ 0)
    (hmass : ∀ p, ρ (j p) = 1)
    (hj : IsFSigma (Submodule.span ℝ (range j) : Set RealL2)) :
    IsFSigma (Submodule.span ℝ (range (fun p => FiniteL2.augment 1 (β • j p))) :
      Set (L2 (Option ℕ))) :=
  isFSigma_span_equiv_family augmentEquiv (augmentedPair β j)
    (isFSigma_span_augmentedPair ρ β hβ j hmass hj)

/-- Any finite family of F-sigma spans has an F-sigma algebraic pure-tensor span. -/
theorem isFSigma_span_pureFin {J : Type*} [Countable J] :
    ∀ (n : ℕ) (P : Fin n → Type*) (j : ∀ i, P i → L2 J),
      (∀ i, IsFSigma (Submodule.span ℝ (range (j i)) : Set (L2 J))) →
      IsFSigma (Submodule.span ℝ (range (fun q : ∀ i, P i =>
        FiniteL2.pureFin n (fun i => j i (q i)))) : Set (L2 (Fin n → J))) := by
  intro n
  induction n with
  | zero =>
    intro P j hj
    letI : Nonempty (∀ i : Fin 0, P i) := ⟨fun i => Fin.elim0 i⟩
    have hrange : range (fun q : ∀ i : Fin 0, P i => FiniteL2.pureFin 0 (fun i => j i (q i))) =
        {lp.single 2 (fun i : Fin 0 => Fin.elim0 i) (1 : ℝ)} := by
      simp [FiniteL2.pureFin]
    rw [hrange]
    exact isFSigma_of_isClosed (Submodule.closed_of_finiteDimensional _)
  | succ n IH =>
    intro P j hj
    let k : (∀ i : Fin n, P i.succ) → L2 (Fin n → J) :=
      fun q => FiniteL2.pureFin n (fun i => j i.succ (q i))
    have hk : IsFSigma (Submodule.span ℝ (range k) : Set (L2 (Fin n → J))) :=
      IH (fun i => P i.succ) (fun i => j i.succ) (fun i => hj i.succ)
    let e := (FiniteL2.reindex (Fin.consEquiv (fun _ : Fin (n + 1) => J))).toContinuousLinearEquiv
    have houter := FiniteTensor.isFSigma_span_outer (j 0) k (hj 0) hk
    have htrans := isFSigma_span_equiv_family e
      (fun p : P 0 × (∀ i : Fin n, P i.succ) => outer (j 0 p.1) (k p.2)) houter
    let pe := Fin.consEquiv P
    have hfun : (fun q : ∀ i, P i => FiniteL2.pureFin (n + 1) (fun i => j i (q i))) ∘ pe =
        e ∘ (fun p : P 0 × (∀ i : Fin n, P i.succ) => outer (j 0 p.1) (k p.2)) := by
      funext p
      rfl
    have hrange : range (fun q : ∀ i, P i => FiniteL2.pureFin (n + 1) (fun i => j i (q i))) =
        range (e ∘ (fun p : P 0 × (∀ i : Fin n, P i.succ) => outer (j 0 p.1) (k p.2))) := by
      rw [← hfun]
      exact (pe.surjective.range_comp _).symm
    rw [hrange]
    exact htrans

end NoUniversalFSigma.PacketSpan

namespace NoUniversalFSigma.PacketSpan
open L2Coordinates

/-- F-sigma algebraic tensor spans for an arbitrary finite index type. -/
theorem isFSigma_span_pure {I J : Type*} [Fintype I] [Countable J]
    (P : I → Type*) (j : ∀ i, P i → L2 J)
    (hj : ∀ i, IsFSigma (Submodule.span ℝ (range (j i)) : Set (L2 J))) :
    IsFSigma (Submodule.span ℝ (range (fun q : ∀ i, P i =>
      FiniteL2.pure (fun i => j i (q i)))) : Set (L2 (I → J))) := by
  let eI := Fintype.equivFin I
  let Pe : Fin (Fintype.card I) → Type _ := fun i => P (eI.symm i)
  let je : ∀ i, Pe i → L2 J := fun i => j (eI.symm i)
  let e := (FiniteL2.reindex (Equiv.arrowCongr eI.symm (Equiv.refl J))).toContinuousLinearEquiv
  have hfin := isFSigma_span_pureFin (Fintype.card I) Pe je (fun i => hj (eI.symm i))
  have htrans := isFSigma_span_equiv_family e
    (fun q : ∀ i, Pe i => FiniteL2.pureFin (Fintype.card I) (fun i => je i (q i))) hfin
  let pe := Equiv.piCongrLeft' P eI
  have hfun : (fun q : ∀ i, P i => FiniteL2.pure (fun i => j i (q i))) =
      (e ∘ (fun q : ∀ i, Pe i => FiniteL2.pureFin (Fintype.card I) (fun i => je i (q i)))) ∘ pe := by
    funext q
    rfl
  have hrange : range (fun q : ∀ i, P i => FiniteL2.pure (fun i => j i (q i))) =
      range (e ∘ (fun q : ∀ i, Pe i => FiniteL2.pureFin (Fintype.card I) (fun i => je i (q i)))) := by
    rw [hfun]
    exact pe.surjective.range_comp _
  rw [hrange]
  exact htrans

/-- The finite augmented packet, including every subset-coordinate component,
has F-sigma algebraic span under the paper's mass-one hypotheses. -/
theorem isFSigma_span_augmentedPure {I : Type*} [Fintype I]
    (P : I → Type*) (j : ∀ i, P i → RealL2) (ρ : I → RealL2 →L[ℝ] ℝ) (β : I → ℝ)
    (hβ : ∀ i, β i ≠ 0) (hmass : ∀ i p, ρ i (j i p) = 1)
    (hj : ∀ i, IsFSigma (Submodule.span ℝ (range (j i)) : Set RealL2)) :
    IsFSigma (Submodule.span ℝ (range (fun q : ∀ i, P i =>
      FiniteL2.pure (fun i => FiniteL2.augment 1 (β i • j i (q i))))) :
      Set (L2 (I → Option ℕ))) := by
  exact isFSigma_span_pure P
    (fun i p => FiniteL2.augment 1 (β i • j i p))
    (fun i => isFSigma_span_augment (j i) (ρ i) (β i) (hβ i) (hmass i) (hj i))

end NoUniversalFSigma.PacketSpan

namespace NoUniversalFSigma.PacketSpan
open L2Coordinates

/-- The finite augmented packet span can be parametrized by the entire infinite
product of the parameter spaces without changing its F-sigma property. -/
theorem isFSigma_span_augmentedAtom (P : ℕ → Type*) [∀ n, Nonempty (P n)]
    (j : ∀ n, P n → RealL2) (ρ : ℕ → RealL2 →L[ℝ] ℝ) (β : ℕ → ℝ)
    (hβ : ∀ n, β n ≠ 0) (hmass : ∀ n p, ρ n (j n p) = 1)
    (hj : ∀ n, IsFSigma (Submodule.span ℝ (range (j n)) : Set RealL2)) (F : Finset ℕ) :
    IsFSigma (Submodule.span ℝ (range (fun q : ∀ n, P n =>
      FiniteL2.augmentedAtom F (fun n => β n • j n (q n)))) :
      Set (FiniteL2.AugmentedPacket F)) := by
  classical
  let g : (∀ n : F, P n) → L2 (F → Option ℕ) := fun q =>
    FiniteL2.pure (fun n : F => FiniteL2.augment 1 (β n • j n (q n)))
  have hg : IsFSigma (Submodule.span ℝ (range g) : Set (L2 (F → Option ℕ))) :=
    isFSigma_span_augmentedPure (fun n : F => P n) (fun n => j n)
      (fun n => ρ n) (fun n => β n) (fun n => hβ n) (fun n => hmass n) (fun n => hj n)
  have hrange : range (fun q : ∀ n, P n =>
      FiniteL2.augmentedAtom F (fun n => β n • j n (q n))) = range g := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨fun n => q n, rfl⟩
    · rintro ⟨q, rfl⟩
      let qe : ∀ n, P n := fun n => if h : n ∈ F then q ⟨n, h⟩ else Classical.choice inferInstance
      refine ⟨qe, ?_⟩
      change FiniteL2.pure (fun n : F => FiniteL2.augment 1 (β n • j n (qe n))) =
        FiniteL2.pure (fun n : F => FiniteL2.augment 1 (β n • j n (q n)))
      congr 1
      funext n
      simp only [qe, dif_pos n.property]
  rw [hrange]
  exact hg

end NoUniversalFSigma.PacketSpan
end
end

/- Source module: NoUniversalFSigma.TensorTail -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Topology
open scoped BigOperators

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2

abbrev Outside (B : Finset ℕ) := {n : ℕ // n ∉ B}
abbrev TailParameter (A : ℕ → AdmissibleFamily) (B : Finset ℕ) :=
  ∀ n : Outside B, (A n).Parameter

/-- Fill the finitely many unused coordinates with fixed parameters. -/
def fill (A : ℕ → AdmissibleFamily) (B : Finset ℕ) (q : TailParameter A B) : Parameter A :=
  fun n => if h : n ∈ B then Classical.choice (A n).nonempty else q ⟨n, h⟩

@[simp] theorem fill_outside (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : TailParameter A B) (n : Outside B) : fill A B q n = q n := by
  simp only [fill, dif_neg n.property]

theorem continuous_fill (A : ℕ → AdmissibleFamily) (B : Finset ℕ) :
    Continuous (fill A B) := by
  apply continuous_pi
  intro n
  by_cases hn : n ∈ B
  · simpa only [fill, dif_pos hn] using
      (continuous_const : Continuous (fun _ : TailParameter A B => Classical.choice (A n).nonempty))
  · simpa only [fill, dif_neg hn] using
      (continuous_apply (⟨n, hn⟩ : Outside B))

def tailFamily (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : TailParameter A B) : L2 (TailIndex B) :=
  tailRestriction B (family A (fill A B q))

theorem continuous_tailFamily (A : ℕ → AdmissibleFamily) (B : Finset ℕ) :
    Continuous (tailFamily A B) :=
  (tailRestriction B).continuous.comp ((continuous_family A).comp (continuous_fill A B))

theorem family_eq_atom (A : ℕ → AdmissibleFamily) (q : Parameter A) (p : FlatIndex) :
    family A q p = atom p.1 (fun n => weight A n • (A n).j (q n)) p.2 := by
  obtain ⟨F, a⟩ := p
  rw [family_apply, atom_apply]
  rfl

theorem tailRestriction_family (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : Parameter A) :
    tailRestriction B (family A q) = tailFamily A B (fun n => q n) := by
  ext p
  rw [tailFamily, tailRestriction_apply, tailRestriction_apply,
    family_eq_atom, family_eq_atom, atom_apply, atom_apply]
  apply Finset.prod_congr rfl
  intro n _
  have hn : (n : ℕ) ∉ B := fun h => Finset.disjoint_left.mp p.property n.property h
  simp only [fill, dif_neg hn]

@[simp] theorem tailFamily_apply (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : TailParameter A B) (p : TailIndex B) :
    tailFamily A B q p = ∏ n : p.val.1,
      weight A n * (A n).j (q ⟨n, fun h => Finset.disjoint_left.mp p.property n.property h⟩)
        (p.val.2 n) := by
  rw [tailFamily, tailRestriction_apply, family_apply]
  apply Finset.prod_congr rfl
  intro n _
  have hn : (n : ℕ) ∉ B := fun h => Finset.disjoint_left.mp p.property n.property h
  simp only [fill, dif_neg hn]

/-- Join an arbitrary finite coefficient packet to a tail-family vector. -/
def mixed (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (v : AugmentedPacket B) (q : TailParameter A B) : Fock :=
  merge B v (tailFamily A B q)

theorem continuous_mixed (A : ℕ → AdmissibleFamily) (B : Finset ℕ) :
    Continuous (fun p : AugmentedPacket B × TailParameter A B => mixed A B p.1 p.2) :=
  (continuous_merge B).comp
    (continuous_fst.prodMk ((continuous_tailFamily A B).comp continuous_snd))

def mixedLinear (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : TailParameter A B) : AugmentedPacket B →L[ℝ] Fock :=
  (split B).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((outerBilinear (I := B → Option ℕ) (J := TailIndex B)).flip (tailFamily A B q))

@[simp] theorem mixedLinear_apply (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : TailParameter A B) (v : AugmentedPacket B) : mixedLinear A B q v = mixed A B v q := rfl

def finiteAtom (A : ℕ → AdmissibleFamily) (B : Finset ℕ) (q : Parameter A) :
    AugmentedPacket B := augmentedAtom B (fun n => weight A n • (A n).j (q n))

def finiteSpan (A : ℕ → AdmissibleFamily) (B : Finset ℕ) : Submodule ℝ (AugmentedPacket B) :=
  Submodule.span ℝ (range (finiteAtom A B))

theorem isFSigma_finiteSpan (A : ℕ → AdmissibleFamily) (B : Finset ℕ) :
    IsFSigma (finiteSpan A B : Set (AugmentedPacket B)) := by
  exact PacketSpan.isFSigma_span_augmentedAtom (fun n => (A n).Parameter)
    (fun n => (A n).j) (fun n => (A n).mass) (weight A)
    (weight_ne_zero A) (fun n => (A n).mass_j) (fun n => (A n).isFSigma_span) B

@[simp] theorem mixed_finiteAtom (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (q : Parameter A) :
    mixed A B (finiteAtom A B q) (fun n => q n) = family A q := by
  rw [mixed, ← tailRestriction_family]
  exact merge_factorization B (family A q) _ (family_eq_atom A q)

/-- Changing finitely many label coordinates does not change the tail vector. -/
theorem mixed_finiteAtom_tail (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (p : Parameter A) (q : TailParameter A B) :
    mixed A B (finiteAtom A B p) q ∈ Submodule.span ℝ (range (family A)) := by
  let r : Parameter A := fun n => if h : n ∈ B then p n else q ⟨n, h⟩
  have hrB : finiteAtom A B r = finiteAtom A B p := by
    ext a
    rw [finiteAtom, finiteAtom, augmentedAtom_apply, augmentedAtom_apply]
    apply Finset.prod_congr rfl
    intro n _
    simp only [r, dif_pos n.property]
  have hrT : (fun n : Outside B => r n) = q := by
    funext n
    simp only [r, dif_neg n.property]
  have h := mixed_finiteAtom A B r
  rw [hrB, hrT] at h
  rw [h]
  exact Submodule.subset_span (mem_range_self r)

theorem mixed_mem_span (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (v : AugmentedPacket B) (hv : v ∈ finiteSpan A B) (q : TailParameter A B) :
    mixed A B v q ∈ Submodule.span ℝ (range (family A)) := by
  change v ∈ (Submodule.span ℝ (range (family A))).comap (mixedLinear A B q).toLinearMap
  apply Submodule.span_le.mpr _ hv
  rintro _ ⟨p, rfl⟩
  exact mixed_finiteAtom_tail A B p q

end NoUniversalFSigma.TensorFamily
end
end

/- Source module: NoUniversalFSigma.TensorSpan -/
section
/-!
# Closed charts for countable tensor spans

The analytic chart lemma formalizes the two-witness argument of Section 6:
bounded continuous linear recovery maps recover each coefficient and, after
division by a scalar bounded away from zero, every individual tail label.
Representations are not required to be unique.
-/

noncomputable section

open Set Filter TopologicalSpace Topology

namespace NoUniversalFSigma.TensorSpan

universe u v w z

section ClosedCharts

variable {N : Type*} {E : Type u} {Z : Type v} {B : N → Type w} {P : N → Type z}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [∀ n, NormedAddCommGroup (B n)] [∀ n, NormedSpace ℝ (B n)]
    [∀ n, TopologicalSpace (P n)]

/-- The closed coefficient requirements in one finite tensor chart. -/
def coefficientCondition {m : ℕ} (S : Fin m → Set E) (ell : Fin m → E →L[ℝ] ℝ)
    (δ K : ℝ) (v : Fin m → E) : Prop :=
  ∀ i, v i ∈ S i ∧ ‖v i‖ ≤ K ∧ δ ≤ |ell i (v i)|

/-- A finite-sum chart, with a closed pinning condition on the tail labels. -/
def recoveredChart {m : ℕ}
    (represent : (Fin m → E) → (Fin m → ∀ n, P n) → Z)
    (S : Fin m → Set E) (ell : Fin m → E →L[ℝ] ℝ) (δ K : ℝ)
    (Pin : Set (Fin m → ∀ n, P n)) : Set Z :=
  {y | ∃ v q, coefficientCondition S ell δ K v ∧ q ∈ Pin ∧ represent v q = y}

/-- Closedness of a chart follows from explicit coefficient and coordinate
recovery. In the countable tensor construction, two disjoint witness packets
supply the coordinate recovery maps, choosing the packet avoiding that
coordinate. -/
theorem isClosed_recoveredChart {m : ℕ}
    (j : ∀ n, P n → B n) (hj : ∀ n, IsClosedEmbedding (j n))
    (represent : (Fin m → E) → (Fin m → ∀ n, P n) → Z)
    (hrepresent : Continuous (fun a : (Fin m → E) × (Fin m → ∀ n, P n) =>
      represent a.1 a.2))
    (S : Fin m → Set E) (hS : ∀ i, IsClosed (S i))
    (ell : Fin m → E →L[ℝ] ℝ) (δ K : ℝ) (hδ : 0 < δ)
    (Pin : Set (Fin m → ∀ n, P n)) (hPin : IsClosed Pin)
    (recoverCoefficient : Fin m → Z →L[ℝ] E)
    (recoverCoordinate : ∀ i : Fin m, ∀ n, Z →L[ℝ] B n)
    (hCoefficient : ∀ v q, coefficientCondition S ell δ K v → q ∈ Pin →
      ∀ i, recoverCoefficient i (represent v q) = v i)
    (hCoordinate : ∀ v q, coefficientCondition S ell δ K v → q ∈ Pin →
      ∀ i n, recoverCoordinate i n (represent v q) = ell i (v i) • j n (q i n)) :
    IsClosed (recoveredChart represent S ell δ K Pin) := by
  apply IsSeqClosed.isClosed
  intro y z hy hz
  choose v q hcond hpin hrep using hy
  let v₀ : Fin m → E := fun i => recoverCoefficient i z
  have hv (i : Fin m) : Tendsto (fun l => v l i) atTop (𝓝 (v₀ i)) := by
    have h := (recoverCoefficient i).continuous.tendsto z |>.comp hz
    change Tendsto (fun l => recoverCoefficient i (y l)) atTop (𝓝 (v₀ i)) at h
    have heq (l : ℕ) : recoverCoefficient i (y l) = v l i := by
      rw [← hrep l]
      exact hCoefficient _ _ (hcond l) (hpin l) i
    simpa only [Function.comp_apply, heq] using h
  have hcond₀ : coefficientCondition S ell δ K v₀ := by
    intro i
    refine ⟨(hS i).mem_of_tendsto (hv i) (Eventually.of_forall fun l => (hcond l i).1), ?_, ?_⟩
    · exact (isClosed_le continuous_norm continuous_const).mem_of_tendsto (hv i)
        (Eventually.of_forall fun l => (hcond l i).2.1)
    · exact (isClosed_le continuous_const ((ell i).continuous.abs)).mem_of_tendsto (hv i)
        (Eventually.of_forall fun l => (hcond l i).2.2)
  have hell₀ (i : Fin m) : ell i (v₀ i) ≠ 0 := by
    intro hzero
    have h := (hcond₀ i).2.2
    rw [hzero, abs_zero] at h
    exact (not_le_of_gt hδ) h
  have hell (l : ℕ) (i : Fin m) : ell i (v l i) ≠ 0 := by
    intro hzero
    have h := (hcond l i).2.2
    rw [hzero, abs_zero] at h
    exact (not_le_of_gt hδ) h
  let b₀ (i : Fin m) (n : N) : B n := (ell i (v₀ i))⁻¹ • recoverCoordinate i n z
  have hjlim (i : Fin m) (n : N) :
      Tendsto (fun l => j n (q l i n)) atTop (𝓝 (b₀ i n)) := by
    have hscalar := ((ell i).continuous.tendsto (v₀ i) |>.comp (hv i)).inv₀ (hell₀ i)
    have hcoord := (recoverCoordinate i n).continuous.tendsto z |>.comp hz
    have heq (l : ℕ) :
        (ell i (v l i))⁻¹ • recoverCoordinate i n (y l) = j n (q l i n) := by
      rw [← hrep l, hCoordinate _ _ (hcond l) (hpin l) i n]
      simp only [smul_smul, inv_mul_cancel₀ (hell l i), one_smul]
    simpa only [Function.comp_apply, heq] using hscalar.smul hcoord
  have hlabel (i : Fin m) (n : N) : ∃ p : P n, j n p = b₀ i n := by
    exact (hj n).isClosed_range.mem_of_tendsto (hjlim i n)
      (Eventually.of_forall fun l => mem_range_self (q l i n))
  choose q₀ hq₀ using hlabel
  have hqpoint (i : Fin m) (n : N) : Tendsto (fun l => q l i n) atTop (𝓝 (q₀ i n)) := by
    apply (hj n).tendsto_nhds_iff.mpr
    rw [hq₀ i n]
    exact hjlim i n
  have hvall : Tendsto v atTop (𝓝 v₀) := tendsto_pi_nhds.mpr hv
  have hqall : Tendsto q atTop (𝓝 q₀) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr (hqpoint i)
  have hPin₀ : q₀ ∈ Pin := hPin.mem_of_tendsto hqall (Eventually.of_forall hpin)
  have hreprlim := (hrepresent.tendsto (v₀, q₀)).comp (hvall.prodMk_nhds hqall)
  have hlast : represent v₀ q₀ = z := by
    apply tendsto_nhds_unique _ hz
    exact hreprlim.congr' (Eventually.of_forall hrep)
  exact ⟨v₀, q₀, hcond₀, hPin₀, hlast⟩

end ClosedCharts

/-- A locally constant function on a separable space has countable range.
This counts the scalar values used to normalize the pinning functionals. -/
theorem countable_range_of_locallyConstant
    {X : Type u} {Y : Type v} [TopologicalSpace X] [SeparableSpace X]
    {f : X → Y} (hf : IsLocallyConstant f) : (range f).Countable := by
  have hd : (range f).PairwiseDisjoint (fun a => f ⁻¹' {a}) := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro x hxa hxb
    exact hab (hxa.symm.trans hxb)
  apply hd.countable_of_isOpen (fun a _ => hf {a})
  intro a ha
  obtain ⟨x, rfl⟩ := ha
  exact ⟨x, rfl⟩

section TailLabels

variable {P : ℕ → Type u}

/-- Two product labels differ in only finitely many coordinates. -/
def TailEquivalent (p q : ∀ n, P n) : Prop := {n | p n ≠ q n}.Finite

theorem tailEquivalent_refl (p : ∀ n, P n) : TailEquivalent p p := by
  simp [TailEquivalent]

theorem tailEquivalent_symm {p q : ∀ n, P n} (h : TailEquivalent p q) :
    TailEquivalent q p := by simpa only [TailEquivalent, ne_comm] using h

theorem tailEquivalent_trans {p q r : ∀ n, P n}
    (hpq : TailEquivalent p q) (hqr : TailEquivalent q r) : TailEquivalent p r := by
  apply (hpq.union hqr).subset
  intro n hn
  by_cases hpqn : p n = q n
  · exact Or.inr (fun hqrn => hn (hpqn.trans hqrn))
  · exact Or.inl hpqn

/-- A finite collection of labels has one common finite exceptional set:
outside it, tail-equivalent labels agree everywhere, while labels in distinct
classes still disagree infinitely often. -/
theorem exists_commonFiniteException {I : Type v} [Finite I]
    (q : I → ∀ n, P n) :
    ∃ B : Finset ℕ, ∀ i j,
      TailEquivalent (q i) (q j) ↔ ∀ n, n ∉ B → q i n = q j n := by
  classical
  let E : I → I → Set ℕ := fun i j =>
    if TailEquivalent (q i) (q j) then {n | q i n ≠ q j n} else ∅
  have hE (i j : I) : (E i j).Finite := by
    dsimp [E]
    split_ifs with h
    · exact h
    · exact finite_empty
  let F : Set ℕ := ⋃ i, ⋃ j, E i j
  have hF : F.Finite := finite_iUnion fun i => finite_iUnion (hE i)
  refine ⟨hF.toFinset, ?_⟩
  intro i j
  constructor
  · intro hij n hn
    by_contra hne
    have hnE : n ∈ E i j := by simpa only [E, if_pos hij] using hne
    have hnF : n ∈ F := mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, hnE⟩⟩
    exact hn (by simpa only [Finite.mem_toFinset] using hnF)
  · intro hout
    apply hF.subset
    intro n hn
    by_contra hnF
    have hnB : n ∉ hF.toFinset := by simpa only [Finite.mem_toFinset] using hnF
    exact hn (hout n hnB)

theorem infinite_tail_disagreements {p q : ∀ n, P n}
    (h : ¬ TailEquivalent p q) (B : Finset ℕ) :
    ({n | p n ≠ q n} \ (B : Set ℕ)).Infinite :=
  (show {n | p n ≠ q n}.Infinite from h).diff B.finite_toSet

/-- Finitely many infinite sets admit mutually distinct chosen elements. -/
theorem exists_injective_finite_choice {I : Type v} [Fintype I]
    (S : I → Set ℕ) (hS : ∀ i, (S i).Infinite) :
    ∃ f : I → ℕ, Function.Injective f ∧ ∀ i, f i ∈ S i := by
  classical
  have hfin : ∀ n : ℕ, ∀ S : Fin n → Set ℕ, (∀ i, (S i).Infinite) →
      ∃ f : Fin n → ℕ, Function.Injective f ∧ ∀ i, f i ∈ S i := by
    intro n
    induction n with
    | zero =>
      intro S _
      exact ⟨Fin.elim0, Function.injective_of_subsingleton _, fun i => Fin.elim0 i⟩
    | succ n ih =>
      intro S hS
      obtain ⟨f, hfi, hfm⟩ := ih (fun i => S i.castSucc) (fun i => hS i.castSucc)
      obtain ⟨k, hkS, hk⟩ := (hS (Fin.last n)).exists_notMem_finite (finite_range f)
      refine ⟨Fin.snoc f k, Fin.snoc_injective_of_injective hfi hk, ?_⟩
      intro i
      induction i using Fin.lastCases with
      | cast i => simpa using hfm i
      | last => simpa using hkS
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  obtain ⟨f, hfi, hfm⟩ := hfin (Fintype.card I) (fun i => S (e i)) (fun i => hS (e i))
  exact ⟨f ∘ e.symm, hfi.comp e.symm.injective, fun i => by simpa using hfm (e.symm i)⟩

/-- Every ordered pair of inequivalent tails receives two distinguishing
coordinates, with all these coordinates mutually distinct and outside the
prescribed finite block. Thus the two witness packets are disjoint. -/
theorem exists_two_witness_coordinates {m : ℕ} (q : Fin m → ∀ n, P n)
    (h : ∀ i j, i ≠ j → ¬ TailEquivalent (q i) (q j)) (B : Finset ℕ) :
    ∃ f : {ij : Fin m × Fin m // ij.1 ≠ ij.2} × Bool → ℕ,
      Function.Injective f ∧ ∀ a,
        f a ∉ B ∧ q a.1.val.1 (f a) ≠ q a.1.val.2 (f a) := by
  let S : ({ij : Fin m × Fin m // ij.1 ≠ ij.2} × Bool) → Set ℕ :=
    fun a => {n | q a.1.val.1 n ≠ q a.1.val.2 n} \ (B : Set ℕ)
  obtain ⟨f, hfi, hfm⟩ := exists_injective_finite_choice S
    (fun a => infinite_tail_disagreements (h _ _ a.1.property) B)
  exact ⟨f, hfi, fun a => ⟨(hfm a).2, (hfm a).1⟩⟩

end TailLabels

section Features

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : Type v} [TopologicalSpace P]

/-- A normalized feature taking the values zero and one at any two prescribed
distinct scalar levels of the same original functional. -/
def normalizedFunctional (mass ell : E →L[ℝ] ℝ) (b c : ℝ) : E →L[ℝ] ℝ :=
  (c - b)⁻¹ • (ell - b • mass)

theorem normalizedFunctional_apply (mass ell : E →L[ℝ] ℝ) (b c : ℝ)
    {x : E} (hx : mass x = 1) :
    normalizedFunctional mass ell b c x = (ell x - b) / (c - b) := by
  simp [normalizedFunctional, hx, div_eq_mul_inv, mul_comm]

theorem normalizedFunctional_one (mass ell : E →L[ℝ] ℝ) {b c : ℝ}
    (hbc : b ≠ c) {x : E} (hx : mass x = 1) (hell : ell x = c) :
    normalizedFunctional mass ell b c x = 1 := by
  rw [normalizedFunctional_apply mass ell b c hx, hell]
  exact div_self (sub_ne_zero.mpr hbc.symm)

theorem normalizedFunctional_zero (mass ell : E →L[ℝ] ℝ) (b c : ℝ)
    {x : E} (hx : mass x = 1) (hell : ell x = b) :
    normalizedFunctional mass ell b c x = 0 := by
  rw [normalizedFunctional_apply mass ell b c hx, hell, sub_self, zero_div]

/-- Countable data indexing the original mass feature and all normalized
features. Including equal scalar levels only adds a harmless zero functional. -/
abbrev FeatureIndex (j : P → E) (ell : ℕ → E →L[ℝ] ℝ) :=
  Unit ⊕ Σ n : ℕ, (range (ell n ∘ j)) × (range (ell n ∘ j))

theorem countable_featureIndex [SeparableSpace P]
    (j : P → E) (ell : ℕ → E →L[ℝ] ℝ)
    (hell : ∀ n, IsLocallyConstant (ell n ∘ j)) : Countable (FeatureIndex j ell) := by
  letI (n : ℕ) : Countable (range (ell n ∘ j)) :=
    (countable_range_of_locallyConstant (hell n)).to_subtype
  infer_instance

/-- The normalized scalar feature indexed by its finite data. -/
def feature (j : P → E) (mass : E →L[ℝ] ℝ) (ell : ℕ → E →L[ℝ] ℝ) :
    FeatureIndex j ell → E →L[ℝ] ℝ
  | .inl _ => mass
  | .inr ⟨n, b, c⟩ => normalizedFunctional mass (ell n) b c

theorem feature_locallyConstant
    (j : P → E) (mass : E →L[ℝ] ℝ) (hmass : ∀ p, mass (j p) = 1)
    (ell : ℕ → E →L[ℝ] ℝ) (hell : ∀ n, IsLocallyConstant (ell n ∘ j))
    (a : FeatureIndex j ell) : IsLocallyConstant (feature j mass ell a ∘ j) := by
  cases a with
  | inl _ =>
    have heq : feature j mass ell (Sum.inl ()) ∘ j = Function.const P (1 : ℝ) :=
      funext hmass
    rw [heq]
    exact IsLocallyConstant.const _
  | inr a =>
    rcases a with ⟨n, b, c⟩
    have heq : feature j mass ell (.inr ⟨n, b, c⟩) ∘ j =
        (fun r : ℝ => (r - b) / (c - b)) ∘ (ell n ∘ j) := by
      funext p
      exact normalizedFunctional_apply mass (ell n) b c (hmass p)
    rw [heq]
    exact (hell n).comp _

/-- Every two distinct labels have a feature equal to one at the first and
zero at the second. The feature index uses values in countable scalar ranges. -/
theorem exists_feature_pin
    (j : P → E) (mass : E →L[ℝ] ℝ) (hmass : ∀ p, mass (j p) = 1)
    (ell : ℕ → E →L[ℝ] ℝ)
    (hsep : ∀ p q, p ≠ q → ∃ n, ell n (j p) ≠ ell n (j q))
    {p q : P} (hpq : p ≠ q) :
    ∃ a : FeatureIndex j ell, feature j mass ell a (j p) = 1 ∧
      feature j mass ell a (j q) = 0 := by
  obtain ⟨n, hn⟩ := hsep p q hpq
  let b : range (ell n ∘ j) := ⟨ell n (j q), ⟨q, rfl⟩⟩
  let c : range (ell n ∘ j) := ⟨ell n (j p), ⟨p, rfl⟩⟩
  exact ⟨.inr ⟨n, b, c⟩,
    normalizedFunctional_one mass (ell n) hn.symm (hmass p) rfl,
    normalizedFunctional_zero mass (ell n) b c (hmass q) rfl⟩

end Features

end NoUniversalFSigma.TensorSpan
end
end

/- Source module: NoUniversalFSigma.TensorRecovery -/
section
noncomputable section

open Set Topology
open scoped BigOperators InnerProduct

namespace NoUniversalFSigma.TensorRecovery

open L2Coordinates FiniteL2

universe u v

theorem inner_outer {I : Type u} {J : Type v}
    (x x' : L2 I) (y y' : L2 J) :
    inner ℝ (outer x y) (outer x' y') = inner ℝ x x' * inner ℝ y y' := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, lp.inner_eq_tsum]
  rw [tsum_mul_tsum_of_summable_norm (lp.summable_inner (𝕜 := ℝ) x x').norm (lp.summable_inner (𝕜 := ℝ) y y').norm]
  apply tsum_congr
  intro p
  simp only [outer_apply, RCLike.inner_apply, conj_trivial]
  ring

theorem inner_pureFin {J : Type v} (n : ℕ) (v w : Fin n → L2 J) :
    inner ℝ (pureFin n v) (pureFin n w) = ∏ i, inner ℝ (v i) (w i) := by
  induction n with
  | zero => simp [pureFin, lp.inner_single_left, lp.single_apply]
  | succ n ih =>
    rw [pureFin, pureFin, LinearIsometryEquiv.inner_map_map,
      inner_outer, ih, Fin.prod_univ_succ]

theorem inner_pure {I : Type u} {J : Type v} [Fintype I] (v w : I → L2 J) :
    inner ℝ (pure v) (pure w) = ∏ i, inner ℝ (v i) (w i) := by
  rw [FiniteL2.pure, FiniteL2.pure, LinearIsometryEquiv.inner_map_map, inner_pureFin]
  exact Fintype.prod_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

theorem inner_atom (F : Finset ℕ) (v w : ℕ → RealL2) :
    inner ℝ (atom F v) (atom F w) = ∏ n : F, inner ℝ (v n) (w n) :=
  inner_pure _ _

/-- Tensor product of a finite collection of bounded scalar functionals. -/
def packetFunctional (W : Finset ℕ) (ell : ℕ → RealL2 →L[ℝ] ℝ) : Packet W →L[ℝ] ℝ :=
  innerSL ℝ (atom W (fun n => (InnerProductSpace.toDual ℝ RealL2).symm (ell n)))

@[simp] theorem packetFunctional_atom (W : Finset ℕ)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) (v : ℕ → RealL2) :
    packetFunctional W ell (atom W v) = ∏ n : W, ell n (v n) := by
  change inner ℝ (atom W _) (atom W v) = _
  rw [inner_atom]
  simp only [InnerProductSpace.toDual_symm_apply]

/-- Contract one factor of a coordinate Hilbert matrix by a bounded functional. -/
def matrixContractRight {I : Type u} {J : Type v}
    (ell : L2 J →L[ℝ] ℝ) : MatrixL2 I J →L[ℝ] L2 I :=
  ContinuousLinearMap.adjoint
    (outerBilinear.flip ((InnerProductSpace.toDual ℝ (L2 J)).symm ell))

@[simp] theorem matrixContractRight_outer {I : Type u} {J : Type v}
    (ell : L2 J →L[ℝ] ℝ) (x : L2 I) (y : L2 J) :
    matrixContractRight ell (outer x y) = ell y • x := by
  apply ext_inner_right ℝ
  intro z
  rw [matrixContractRight, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (outer x y) (outer z _) = _
  rw [inner_outer, real_inner_comm ((InnerProductSpace.toDual ℝ (L2 J)).symm ell) y,
    InnerProductSpace.toDual_symm_apply]
  simp only [real_inner_smul_left, mul_comm]

/-- Contract a disjoint finite witness block after reordering its factors. -/
def packetContraction (F W : Finset ℕ) (h : Disjoint F W)
    (ell : Packet W →L[ℝ] ℝ) : Packet (F ∪ W) →L[ℝ] Packet F :=
  (matrixContractRight ell).comp (packetUnion F W h).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem packetContraction_atom (F W : Finset ℕ) (h : Disjoint F W)
    (ell : Packet W →L[ℝ] ℝ) (v : ℕ → RealL2) :
    packetContraction F W h ell (atom (F ∪ W) v) = ell (atom W v) • atom F v := by
  change matrixContractRight ell (packetUnion F W h (atom (F ∪ W) v)) = _
  rw [packetUnion_atom, matrixContractRight_outer]

/-- Contract the coefficient factor of a coordinate Hilbert matrix. -/
def matrixContractLeft {I : Type u} {J : Type v}
    (ell : L2 I →L[ℝ] ℝ) : MatrixL2 I J →L[ℝ] L2 J :=
  ContinuousLinearMap.adjoint
    (outerBilinear ((InnerProductSpace.toDual ℝ (L2 I)).symm ell))

@[simp] theorem matrixContractLeft_outer {I : Type u} {J : Type v}
    (ell : L2 I →L[ℝ] ℝ) (x : L2 I) (y : L2 J) :
    matrixContractLeft ell (outer x y) = ell x • y := by
  apply ext_inner_right ℝ
  intro z
  rw [matrixContractLeft, ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (outer x y) (outer _ z) = _
  rw [inner_outer, real_inner_comm ((InnerProductSpace.toDual ℝ (L2 I)).symm ell) x,
    InnerProductSpace.toDual_symm_apply]
  simp only [real_inner_smul_left]

end NoUniversalFSigma.TensorRecovery
end
end

/- Source module: NoUniversalFSigma.TailRecovery -/
section
noncomputable section
open Set Topology
open scoped BigOperators

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2 TensorRecovery

def tailBlockIndex (B F : Finset ℕ) (h : Disjoint F B) (a : F → ℕ) : TailIndex B :=
  ⟨⟨F, a⟩, h⟩

theorem tailBlockIndex_injective (B F : Finset ℕ) (h : Disjoint F B) :
    Function.Injective (tailBlockIndex B F h) := by
  intro a b hab
  exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val hab)).2

def tailBlock (B F : Finset ℕ) (h : Disjoint F B) : L2 (TailIndex B) →L[ℝ] Packet F :=
  restrictCLM (tailBlockIndex B F h) (tailBlockIndex_injective B F h)

@[simp] theorem tailBlock_tailFamily (A : ℕ → AdmissibleFamily) (B F : Finset ℕ)
    (h : Disjoint F B) (q : TailParameter A B) :
    tailBlock B F h (tailFamily A B q) = component A (fill A B q) F := by
  ext a
  exact congrArg (fun x : Packet F => x a) (block_family A (fill A B q) F)

def weightProduct (A : ℕ → AdmissibleFamily) (F : Finset ℕ) : ℝ := ∏ n : F, weight A n

theorem weightProduct_ne_zero (A : ℕ → AdmissibleFamily) (F : Finset ℕ) :
    weightProduct A F ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun n _ => weight_ne_zero A n)

def witnessValue (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) (q : TailParameter A B) : ℝ :=
  ∏ n : W, ell n ((A n).j (fill A B q n))

def tailWitness (A : ℕ → AdmissibleFamily) (B W : Finset ℕ) (h : Disjoint W B)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) : L2 (TailIndex B) →L[ℝ] ℝ :=
  (weightProduct A W)⁻¹ • ((packetFunctional W ell).comp (tailBlock B W h))

@[simp] theorem tailWitness_tailFamily (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (h : Disjoint W B) (ell : ℕ → RealL2 →L[ℝ] ℝ) (q : TailParameter A B) :
    tailWitness A B W h ell (tailFamily A B q) = witnessValue A B W ell q := by
  simp only [tailWitness, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    tailBlock_tailFamily, component, atom_smul, map_smul, packetFunctional_atom,
    weightProduct, witnessValue, smul_eq_mul]
  rw [← mul_assoc]
  change ((weightProduct A W)⁻¹ * weightProduct A W) * witnessValue A B W ell q = _
  rw [inv_mul_cancel₀ (weightProduct_ne_zero A W), one_mul]
  rfl

/-- A finite witness packet recovers the entire finite coefficient packet. -/
def recoverCoefficient (A : ℕ → AdmissibleFamily) (B W : Finset ℕ) (h : Disjoint W B)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) : Fock →L[ℝ] AugmentedPacket B :=
  (matrixContractRight (tailWitness A B W h ell)).comp
    (split B).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem recoverCoefficient_mixed (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (h : Disjoint W B) (ell : ℕ → RealL2 →L[ℝ] ℝ)
    (v : AugmentedPacket B) (q : TailParameter A B) :
    recoverCoefficient A B W h ell (mixed A B v q) = witnessValue A B W ell q • v := by
  change matrixContractRight (tailWitness A B W h ell)
    (split B ((split B).symm (outer v (tailFamily A B q)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, matrixContractRight_outer, tailWitness_tailFamily]

def afterCoefficient (B : Finset ℕ) (lam : AugmentedPacket B →L[ℝ] ℝ) :
    Fock →L[ℝ] L2 (TailIndex B) :=
  (matrixContractLeft lam).comp (split B).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem afterCoefficient_mixed (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    (lam : AugmentedPacket B →L[ℝ] ℝ) (v : AugmentedPacket B) (q : TailParameter A B) :
    afterCoefficient B lam (mixed A B v q) = lam v • tailFamily A B q := by
  change matrixContractLeft lam (split B ((split B).symm (outer v (tailFamily A B q)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, matrixContractLeft_outer]

def recoverTailCoordinate (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (hWB : Disjoint W B) (n : Outside B) (hnW : (n : ℕ) ∉ W)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) : L2 (TailIndex B) →L[ℝ] RealL2 :=
  let hnW' : Disjoint ({(n : ℕ)} : Finset ℕ) W := Finset.disjoint_singleton_left.mpr hnW
  let hUB : Disjoint ({(n : ℕ)} ∪ W) B :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_singleton_left.mpr n.property, hWB⟩
  (weightProduct A W * weight A n)⁻¹ •
    ((packetSingleton n).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((packetContraction {(n : ℕ)} W hnW' (packetFunctional W ell)).comp (tailBlock B _ hUB)))

@[simp] theorem recoverTailCoordinate_tailFamily (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (hWB : Disjoint W B) (n : Outside B) (hnW : (n : ℕ) ∉ W)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) (q : TailParameter A B) :
    recoverTailCoordinate A B W hWB n hnW ell (tailFamily A B q) =
      witnessValue A B W ell q • (A n).j (q n) := by
  simp only [recoverTailCoordinate, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, tailBlock_tailFamily, component,
    packetContraction_atom, map_smul]
  change (weightProduct A W * weight A n)⁻¹ •
    ((packetFunctional W ell (atom W (fun k => weight A k • (A k).j (fill A B q k)))) •
      packetSingleton n (atom {↑n} (fun k => weight A k • (A k).j (fill A B q k)))) = _
  rw [packetSingleton_atom, atom_smul, map_smul, packetFunctional_atom]
  simp only [fill_outside, smul_eq_mul]
  rw [smul_smul, smul_smul]
  have hscalar : (weightProduct A W * weight A n)⁻¹ *
      (weightProduct A W * witnessValue A B W ell q) * weight A n =
      witnessValue A B W ell q := by
    field_simp [weightProduct_ne_zero A W, weight_ne_zero A n]
  exact congrArg (fun r : ℝ => r • (A n).j (q n)) hscalar

def recoverCoordinate (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (hWB : Disjoint W B) (n : Outside B) (hnW : (n : ℕ) ∉ W)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) (lam : AugmentedPacket B →L[ℝ] ℝ) :
    Fock →L[ℝ] RealL2 :=
  (recoverTailCoordinate A B W hWB n hnW ell).comp (afterCoefficient B lam)

@[simp] theorem recoverCoordinate_mixed (A : ℕ → AdmissibleFamily) (B W : Finset ℕ)
    (hWB : Disjoint W B) (n : Outside B) (hnW : (n : ℕ) ∉ W)
    (ell : ℕ → RealL2 →L[ℝ] ℝ) (lam : AugmentedPacket B →L[ℝ] ℝ)
    (v : AugmentedPacket B) (q : TailParameter A B) :
    recoverCoordinate A B W hWB n hnW ell lam (mixed A B v q) =
      (lam v * witnessValue A B W ell q) • (A n).j (q n) := by
  simp only [recoverCoordinate, ContinuousLinearMap.comp_apply, afterCoefficient_mixed,
    map_smul, recoverTailCoordinate_tailFamily, smul_smul]

end NoUniversalFSigma.TensorFamily
end
end

/- Source module: NoUniversalFSigma.TensorPinning -/
section
noncomputable section
open Set TopologicalSpace Topology
open scoped BigOperators
namespace NoUniversalFSigma.TensorSpan
universe u v w

section PinningData
variable {N : Type u} {E : N → Type v} {P : N → Type w}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
  [∀ n, TopologicalSpace (P n)]

/-- Finite, countably indexed scalar features used to distinguish tail labels. -/
abbrev PinningData (j : ∀ n, P n → E n) (ell : ∀ n, ℕ → E n →L[ℝ] ℝ) (m : ℕ) :=
  Σ W : Finset N, Fin m → ∀ n : W, FeatureIndex (j n) (ell n)

theorem countable_pinningData [Countable N] [∀ n, SeparableSpace (P n)]
    (j : ∀ n, P n → E n) (ell : ∀ n, ℕ → E n →L[ℝ] ℝ)
    (hell : ∀ n k, IsLocallyConstant (ell n k ∘ j n)) (m : ℕ) :
    Countable (PinningData j ell m) := by
  letI (n : N) : Countable (FeatureIndex (j n) (ell n)) :=
    countable_featureIndex (j n) (ell n) (hell n)
  infer_instance

def pinningValue (j : ∀ n, P n → E n) (mass : ∀ n, E n →L[ℝ] ℝ)
    (ell : ∀ n, ℕ → E n →L[ℝ] ℝ) {m : ℕ} (D : PinningData j ell m)
    (c : Fin m) (q : ∀ n, P n) : ℝ :=
  ∏ n : D.1, feature (j n) (mass n) (ell n) (D.2 c n) (j n (q n))

def pinningCondition (j : ∀ n, P n → E n) (mass : ∀ n, E n →L[ℝ] ℝ)
    (ell : ∀ n, ℕ → E n →L[ℝ] ℝ) {m : ℕ} (D : PinningData j ell m) :
    Set (Fin m → ∀ n, P n) :=
  {q | ∀ c d, pinningValue j mass ell D c (q d) = if c = d then 1 else 0}

theorem continuous_pinningValue
    (j : ∀ n, P n → E n) (mass : ∀ n, E n →L[ℝ] ℝ)
    (hmass : ∀ n p, mass n (j n p) = 1)
    (ell : ∀ n, ℕ → E n →L[ℝ] ℝ)
    (hell : ∀ n k, IsLocallyConstant (ell n k ∘ j n))
    {m : ℕ} (D : PinningData j ell m) (c : Fin m) :
    Continuous (pinningValue j mass ell D c) := by
  apply continuous_finsetProd
  intro n _
  exact (feature_locallyConstant (j n) (mass n) (hmass n) (ell n) (hell n)
    (D.2 c n)).continuous.comp (continuous_apply (n : N))

theorem isClosed_pinningCondition
    (j : ∀ n, P n → E n) (mass : ∀ n, E n →L[ℝ] ℝ)
    (hmass : ∀ n p, mass n (j n p) = 1)
    (ell : ∀ n, ℕ → E n →L[ℝ] ℝ)
    (hell : ∀ n k, IsLocallyConstant (ell n k ∘ j n))
    {m : ℕ} (D : PinningData j ell m) :
    IsClosed (pinningCondition j mass ell D) := by
  change IsClosed {q | ∀ c d, _}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro d
  exact isClosed_eq ((continuous_pinningValue j mass hmass ell hell D c).comp
    (continuous_apply d)) continuous_const

end PinningData



/-- Two disjoint finite packets pin any finite collection of labels once
mutually distinct distinguishing coordinates have been chosen. -/
theorem exists_two_pinningData
    {N : Type u} {E : N → Type v} {P : N → Type w}
    [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace ℝ (E n)]
    [∀ n, TopologicalSpace (P n)]
    (j : ∀ n, P n → E n) (mass : ∀ n, E n →L[ℝ] ℝ)
    (hmass : ∀ n p, mass n (j n p) = 1)
    (ell : ∀ n, ℕ → E n →L[ℝ] ℝ)
    (hsep : ∀ n p q, p ≠ q → ∃ k, ell n k (j n p) ≠ ell n k (j n q))
    {m : ℕ} (q : Fin m → ∀ n, P n)
    (f : {ij : Fin m × Fin m // ij.1 ≠ ij.2} × Bool → N)
    (hf : Function.Injective f)
    (hq : ∀ a, q a.1.val.1 (f a) ≠ q a.1.val.2 (f a)) :
    ∃ D : Bool → PinningData j ell m,
      Disjoint (D false).1 (D true).1 ∧
      (∀ r, q ∈ pinningCondition j mass ell (D r)) ∧
      ∀ r n, n ∈ (D r).1 → ∃ a, f (a, r) = n := by
  classical
  let Pair := {ij : Fin m × Fin m // ij.1 ≠ ij.2}
  have hpins (a : Pair) (r : Bool) :
      ∃ t : FeatureIndex (j (f (a, r))) (ell (f (a, r))),
        feature (j (f (a, r))) (mass (f (a, r))) (ell (f (a, r))) t
          (j (f (a, r)) (q a.val.1 (f (a, r)))) = 1 ∧
        feature (j (f (a, r))) (mass (f (a, r))) (ell (f (a, r))) t
          (j (f (a, r)) (q a.val.2 (f (a, r)))) = 0 :=
    exists_feature_pin _ _ (hmass _) _ (hsep _) (hq (a, r))
  choose t ht1 ht0 using hpins
  let W (r : Bool) : Finset N := Finset.univ.image (fun a : Pair => f (a, r))
  have hW (r : Bool) (n : W r) : ∃ a : Pair, f (a, r) = n := by
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp n.property
    exact ⟨a, ha⟩
  choose pair hpair using hW
  have eval_transport (a : Pair) (r : Bool) (n : N) (hn : f (a, r) = n)
      (c : Fin m) :
      feature (j n) (mass n) (ell n) (hn ▸ t a r) (j n (q c n)) =
        feature (j (f (a, r))) (mass (f (a, r))) (ell (f (a, r))) (t a r)
          (j (f (a, r)) (q c (f (a, r)))) := by
    subst n
    rfl
  have hpair_eq (a : Pair) (r : Bool) (hn : f (a, r) ∈ W r) :
      pair r ⟨f (a, r), hn⟩ = a := by
    exact Prod.mk.inj (hf (hpair r ⟨f (a, r), hn⟩)) |>.1
  let T (r : Bool) (c : Fin m) (n : W r) : FeatureIndex (j n) (ell n) :=
    if hc : c = (pair r n).val.1 then
      hpair r n ▸ t (pair r n) r
    else Sum.inl ()
  let D (r : Bool) : PinningData j ell m := ⟨W r, T r⟩
  refine ⟨D, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro n hn0 hn1
    have ha := hpair false ⟨n, hn0⟩
    have hb := hpair true ⟨n, hn1⟩
    have hbool := (Prod.mk.inj (hf (ha.trans hb.symm))).2
    cases hbool
  · intro r c d
    change (∏ n : W r, feature (j n) (mass n) (ell n) (T r c n) (j n (q d n))) = _
    by_cases hcd : c = d
    · subst d
      rw [if_pos rfl]
      apply Finset.prod_eq_one
      intro n _
      dsimp [T]
      split_ifs with hc
      · rw [eval_transport, hc]
        exact ht1 (pair r n) r
      · exact hmass n _
    · rw [if_neg hcd]
      let a : Pair := ⟨(c, d), hcd⟩
      have hn : f (a, r) ∈ W r := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨f (a, r), hn⟩ : W r))
      let n : W r := ⟨f (a, r), hn⟩
      have hp : pair r n = a := hpair_eq a r hn
      have hc : c = (pair r n).val.1 := by rw [hp]
      change feature (j n) (mass n) (ell n) (T r c n) (j n (q d n)) = 0
      dsimp [T]
      rw [if_pos hc, eval_transport, hp]
      exact ht0 a r
  · intro r n hn
    exact ⟨pair r ⟨n, hn⟩, hpair r ⟨n, hn⟩⟩

end NoUniversalFSigma.TensorSpan
end
end

/- Source module: NoUniversalFSigma.TensorCharts -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open Set TopologicalSpace Topology
open scoped BigOperators
namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2 TensorSpan

abbrev PinData (A : ℕ → AdmissibleFamily) (m : ℕ) :=
  PinningData (fun n => (A n).j) (fun n => (A n).separator) m

theorem countable_pinData (A : ℕ → AdmissibleFamily) (m : ℕ) :
    Countable (PinData A m) :=
  countable_pinningData _ _ (fun n => (A n).locallyConstant_separator) m

def pinFunctionals (A : ℕ → AdmissibleFamily) {m : ℕ} (D : PinData A m)
    (c : Fin m) (n : ℕ) : RealL2 →L[ℝ] ℝ :=
  if hn : n ∈ D.1 then
    feature (A n).j (A n).mass (A n).separator (D.2 c ⟨n, hn⟩)
  else (A n).mass

theorem witnessValue_pinFunctionals (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    {m : ℕ} (D : PinData A m) (c : Fin m) (q : TailParameter A B) :
    witnessValue A B D.1 (pinFunctionals A D c) q =
      pinningValue (fun n => (A n).j) (fun n => (A n).mass)
        (fun n => (A n).separator) D c (fill A B q) := by
  apply Finset.prod_congr rfl
  intro n _
  simp only [pinFunctionals, dif_pos n.property]

def pinSet (A : ℕ → AdmissibleFamily) (B : Finset ℕ) {m : ℕ}
    (D : Bool → PinData A m) : Set (Fin m → TailParameter A B) :=
  {q | ∀ r, (fun c => fill A B (q c)) ∈
    pinningCondition (fun n => (A n).j) (fun n => (A n).mass)
      (fun n => (A n).separator) (D r)}

theorem isClosed_pinSet (A : ℕ → AdmissibleFamily) (B : Finset ℕ) {m : ℕ}
    (D : Bool → PinData A m) : IsClosed (pinSet A B D) := by
  change IsClosed {q | ∀ r, _}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro r
  apply (isClosed_pinningCondition (fun n => (A n).j) (fun n => (A n).mass)
    (fun n => (A n).mass_j) (fun n => (A n).separator)
    (fun n => (A n).locallyConstant_separator) (D r)).preimage
  exact continuous_pi fun c => (continuous_fill A B).comp (continuous_apply c)

def represent (A : ℕ → AdmissibleFamily) (B : Finset ℕ) (m : ℕ)
    (v : Fin m → AugmentedPacket B) (q : Fin m → TailParameter A B) : Fock :=
  ∑ i, mixed A B (v i) (q i)

theorem continuous_represent (A : ℕ → AdmissibleFamily) (B : Finset ℕ) (m : ℕ) :
    Continuous (fun p : (Fin m → AugmentedPacket B) × (Fin m → TailParameter A B) =>
      represent A B m p.1 p.2) := by
  change Continuous (fun p : (Fin m → AugmentedPacket B) × (Fin m → TailParameter A B) =>
    ∑ i, mixed A B (p.1 i) (p.2 i))
  apply continuous_finsetSum
  intro i _
  have h : Continuous (fun p : (Fin m → AugmentedPacket B) × (Fin m → TailParameter A B) =>
      (p.1 i, p.2 i)) :=
    ((continuous_apply i).comp continuous_fst).prodMk
      ((continuous_apply i).comp continuous_snd)
  exact (continuous_mixed A B).comp h

theorem recoverCoefficient_represent (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    {m : ℕ} (D : Bool → PinData A m) (hWB : ∀ r, Disjoint (D r).1 B)
    (v : Fin m → AugmentedPacket B) (q : Fin m → TailParameter A B)
    (hq : q ∈ pinSet A B D) (c : Fin m) (r : Bool) :
    recoverCoefficient A B (D r).1 (hWB r) (pinFunctionals A (D r) c)
      (represent A B m v q) = v c := by
  have hp (d : Fin m) := hq r c d
  simp only [represent, map_sum, recoverCoefficient_mixed,
    witnessValue_pinFunctionals, hp]
  simp

def coordinateWitness {m : ℕ} {A : ℕ → AdmissibleFamily}
    (D : Bool → PinData A m) (n : ℕ) : Bool :=
  if n ∈ (D false).1 then true else false

theorem not_mem_coordinateWitness {m : ℕ} {A : ℕ → AdmissibleFamily}
    (D : Bool → PinData A m) (hD : Disjoint (D false).1 (D true).1) (n : ℕ) :
    n ∉ (D (coordinateWitness D n)).1 := by
  by_cases hn : n ∈ (D false).1
  · simp only [coordinateWitness, if_pos hn]
    exact fun hn' => Finset.disjoint_left.mp hD hn hn'
  · simpa only [coordinateWitness, if_neg hn] using hn

def chartCoordinateRecovery (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    {m : ℕ} (D : Bool → PinData A m) (hWB : ∀ r, Disjoint (D r).1 B)
    (hD : Disjoint (D false).1 (D true).1)
    (lam : Fin m → AugmentedPacket B →L[ℝ] ℝ) (c : Fin m) (n : Outside B) :
    Fock →L[ℝ] RealL2 :=
  recoverCoordinate A B (D (coordinateWitness D n)).1 (hWB _) n
    (not_mem_coordinateWitness D hD n) (pinFunctionals A (D (coordinateWitness D n)) c) (lam c)

theorem chartCoordinateRecovery_represent (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    {m : ℕ} (D : Bool → PinData A m) (hWB : ∀ r, Disjoint (D r).1 B)
    (hD : Disjoint (D false).1 (D true).1)
    (lam : Fin m → AugmentedPacket B →L[ℝ] ℝ)
    (v : Fin m → AugmentedPacket B) (q : Fin m → TailParameter A B)
    (hq : q ∈ pinSet A B D) (c : Fin m) (n : Outside B) :
    chartCoordinateRecovery A B D hWB hD lam c n (represent A B m v q) =
      lam c (v c) • (A n).j (q c n) := by
  have hp (d : Fin m) := hq (coordinateWitness D n) c d
  simp only [chartCoordinateRecovery, represent, map_sum, recoverCoordinate_mixed,
    witnessValue_pinFunctionals, hp]
  simp

def tensorChart (A : ℕ → AdmissibleFamily) (B : Finset ℕ) {m : ℕ}
    (D : Bool → PinData A m) (S : Fin m → Set (AugmentedPacket B))
    (lam : Fin m → AugmentedPacket B →L[ℝ] ℝ) (δ K : ℝ) : Set Fock :=
  recoveredChart (represent A B m) S lam δ K (pinSet A B D)

theorem isClosed_tensorChart (A : ℕ → AdmissibleFamily) (B : Finset ℕ) {m : ℕ}
    (D : Bool → PinData A m) (hWB : ∀ r, Disjoint (D r).1 B)
    (hD : Disjoint (D false).1 (D true).1)
    (S : Fin m → Set (AugmentedPacket B)) (hS : ∀ i, IsClosed (S i))
    (lam : Fin m → AugmentedPacket B →L[ℝ] ℝ) (δ K : ℝ) (hδ : 0 < δ) :
    IsClosed (tensorChart A B D S lam δ K) := by
  apply isClosed_recoveredChart (fun n : Outside B => (A n).j)
    (fun n => (A n).closedEmbedding_j) (represent A B m) (continuous_represent A B m)
    S hS lam δ K hδ (pinSet A B D) (isClosed_pinSet A B D)
    (fun c => recoverCoefficient A B (D false).1 (hWB false) (pinFunctionals A (D false) c))
    (chartCoordinateRecovery A B D hWB hD lam)
  · intro v q _ hq c
    exact recoverCoefficient_represent A B D hWB v q hq c false
  · intro v q _ hq c n
    exact chartCoordinateRecovery_represent A B D hWB hD lam v q hq c n

theorem tensorChart_subset_span (A : ℕ → AdmissibleFamily) (B : Finset ℕ) {m : ℕ}
    (D : Bool → PinData A m) (S : Fin m → Set (AugmentedPacket B))
    (hS : ∀ i, S i ⊆ finiteSpan A B)
    (lam : Fin m → AugmentedPacket B →L[ℝ] ℝ) (δ K : ℝ) :
    tensorChart A B D S lam δ K ⊆ Submodule.span ℝ (range (family A)) := by
  rintro y ⟨v, q, hv, _, rfl⟩
  exact Submodule.sum_mem _ (fun i _ => mixed_mem_span A B (v i) (hS i (hv i).1) (q i))




/-- The two finite witness packets can be chosen outside the finite coefficient
block, simultaneously pinning every member of an inequivalent finite family. -/
theorem exists_pinned_tail_data (A : ℕ → AdmissibleFamily) (B : Finset ℕ)
    {m : ℕ} (q : Fin m → Parameter A)
    (hq : ∀ i j, i ≠ j → ¬ TailEquivalent (q i) (q j)) :
    ∃ D : Bool → PinData A m,
      (∀ r, Disjoint (D r).1 B) ∧
      Disjoint (D false).1 (D true).1 ∧
      (fun c => fun n : Outside B => q c n) ∈ pinSet A B D := by
  classical
  obtain ⟨f, hf, hfm⟩ := exists_two_witness_coordinates q hq B
  obtain ⟨D, hD, hpin, hsupp⟩ := exists_two_pinningData
    (fun n => (A n).j) (fun n => (A n).mass) (fun n => (A n).mass_j)
    (fun n => (A n).separator) (fun n => (A n).separates) q f hf (fun a => (hfm a).2)
  have hWB (r : Bool) : Disjoint (D r).1 B := by
    apply Finset.disjoint_left.mpr
    intro n hn hB
    obtain ⟨a, rfl⟩ := hsupp r n hn
    exact (hfm (a, r)).1 hB
  refine ⟨D, hWB, hD, ?_⟩
  intro r c d
  have heq : pinningValue (fun n => (A n).j) (fun n => (A n).mass)
      (fun n => (A n).separator) (D r) c
        (fill A B (fun n : Outside B => q d n)) =
      pinningValue (fun n => (A n).j) (fun n => (A n).mass)
        (fun n => (A n).separator) (D r) c (q d) := by
    apply Finset.prod_congr rfl
    intro n _
    have hn : (n : ℕ) ∉ B := fun h => Finset.disjoint_left.mp (hWB r) n.property h
    simp only [fill, dif_neg hn]
  exact heq.trans (hpin r c d)

end NoUniversalFSigma.TensorFamily
end
end

/- Source module: NoUniversalFSigma.TensorCover -/
section
noncomputable section
open Set
open scoped BigOperators

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2 TensorSpan

/-- Regroup a finite sum of product atoms by tail equivalence, removing zero
coefficient packets after cancellation. -/
theorem regroup_finite_sum (A : ℕ → AdmissibleFamily) {I : Type*} [Fintype I]
    (c : I → ℝ) (q : I → Parameter A) :
    ∃ (m : ℕ) (B : Finset ℕ) (v : Fin m → AugmentedPacket B) (p : Fin m → Parameter A),
      (∀ i, v i ∈ finiteSpan A B ∧ v i ≠ 0) ∧
      (∀ i j, i ≠ j → ¬ TailEquivalent (p i) (p j)) ∧
      (∑ i, c i • family A (q i)) =
        ∑ i, mixed A B (v i) (fun n => p i n) := by
  classical
  obtain ⟨B, hB⟩ := exists_commonFiniteException q
  let r : I → TailParameter A B := fun i n => q i n
  let S : Finset (TailParameter A B) := Finset.univ.image r
  let v : TailParameter A B → AugmentedPacket B := fun s =>
    ∑ i ∈ Finset.univ.filter (fun i => r i = s), c i • finiteAtom A B (q i)
  let p : TailParameter A B → Parameter A := fun s =>
    if h : ∃ i, r i = s then q (Classical.choose h) else fun n => Classical.choice (A n).nonempty
  have hsource : ∀ s ∈ S, ∃ i, p s = q i ∧ r i = s := by
    intro s hs
    have hex : ∃ i, r i = s := by
      obtain ⟨i, hi, hri⟩ := Finset.mem_image.mp hs
      exact ⟨i, hri⟩
    exact ⟨Classical.choose hex, by simp only [p, dif_pos hex], Classical.choose_spec hex⟩
  have htail : ∀ s ∈ S, (fun n : Outside B => p s n) = s := by
    intro s hs
    obtain ⟨i, hi, hri⟩ := hsource s hs
    exact hi ▸ hri
  have hvmem : ∀ s, v s ∈ finiteSpan A B := by
    intro s
    exact Submodule.sum_mem _ fun i hi =>
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self (q i)))
  have hgroup : ∀ s, mixed A B (v s) s =
      ∑ i ∈ Finset.univ.filter (fun i => r i = s), c i • family A (q i) := by
    intro s
    change mixedLinear A B s (v s) = _
    dsimp only [v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, mixedLinear_apply]
    have hri : r i = s := (Finset.mem_filter.mp hi).2
    rw [← hri]
    exact congrArg (fun z => c i • z) (mixed_finiteAtom A B (q i))
  have hsum : (∑ i, c i • family A (q i)) = ∑ s ∈ S, mixed A B (v s) s := by
    symm
    simp_rw [hgroup]
    exact Finset.sum_fiberwise_of_maps_to
      (fun i hi => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) _
  let T := S.filter (fun s => v s ≠ 0)
  have hsumT : (∑ s ∈ S, mixed A B (v s) s) = ∑ s ∈ T, mixed A B (v s) s := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hsT
    have hvzero : v s = 0 := by
      by_contra hvne
      exact hsT (Finset.mem_filter.mpr ⟨hs, hvne⟩)
    change mixedLinear A B s (v s) = 0
    simp only [hvzero, map_zero]
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine ⟨Fintype.card T, B, (fun i => v (e i)), (fun i => p (e i)), ?_, ?_, ?_⟩
  · intro i
    exact ⟨hvmem _, (Finset.mem_filter.mp (e i).property).2⟩
  · intro i j hij htailEq
    obtain ⟨a, ha, hra⟩ := hsource (e i) (Finset.mem_filter.mp (e i).property).1
    obtain ⟨b, hb, hrb⟩ := hsource (e j) (Finset.mem_filter.mp (e j).property).1
    have hab : TailEquivalent (q a) (q b) := by simpa only [← ha, ← hb] using htailEq
    have hout := (hB a b).mp hab
    have hreq : r a = r b := funext fun n => hout n n.property
    have heq : (e i : TailParameter A B) = e j := hra.symm.trans (hreq.trans hrb)
    exact hij (e.injective (Subtype.ext heq))
  · apply (hsum.trans hsumT).trans
    rw [← Finset.sum_coe_sort]
    symm
    apply Fintype.sum_equiv e
    intro i
    rw [htail (e i) (Finset.mem_filter.mp (e i).property).1]

end NoUniversalFSigma.TensorFamily

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2 TensorSpan

/-- Every element of the actual algebraic countable tensor span has a finite
mixed representation with nonzero coefficient packets and inequivalent tails. -/
theorem exists_mixed_representation (A : ℕ → AdmissibleFamily) {y : Fock}
    (hy : y ∈ Submodule.span ℝ (range (family A))) :
    ∃ (m : ℕ) (B : Finset ℕ) (v : Fin m → AugmentedPacket B) (q : Fin m → Parameter A),
      (∀ i, v i ∈ finiteSpan A B ∧ v i ≠ 0) ∧
      (∀ i j, i ≠ j → ¬ TailEquivalent (q i) (q j)) ∧
      y = ∑ i, mixed A B (v i) (fun n => q i n) := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  have hsum : (∑ p : c.support, c p • family A p) = y := by
    exact (Finset.sum_coe_sort c.support (fun p => c p • family A p)).trans hc
  obtain ⟨m, B, v, q, hv, hq, heq⟩ :=
    regroup_finite_sum A (fun p : c.support => c p) (fun p => p.val)
  exact ⟨m, B, v, q, hv, hq, hsum.symm.trans heq⟩

end NoUniversalFSigma.TensorFamily

namespace NoUniversalFSigma.TensorSpan

/-- One integer simultaneously bounds finitely many coefficient norms and
keeps finitely many nonzero scalar evaluations uniformly away from zero. -/
theorem exists_uniform_chart_bounds {I E : Type*} [Fintype I] [NormedAddCommGroup E]
    (v : I → E) (a : I → ℝ) (ha : ∀ i, a i ≠ 0) :
    ∃ K : ℕ, ∀ i, ‖v i‖ ≤ K ∧ (1 : ℝ) / (K + 1) ≤ |a i| := by
  classical
  obtain ⟨K, hK⟩ := exists_nat_gt (max (∑ i, ‖v i‖) (∑ i, (|a i|)⁻¹))
  refine ⟨K, ?_⟩
  intro i
  have hnorm : ‖v i‖ ≤ ∑ j, ‖v j‖ :=
    Finset.single_le_sum (fun j hj => norm_nonneg (v j)) (Finset.mem_univ i)
  have hinv : (|a i|)⁻¹ ≤ ∑ j, (|a j|)⁻¹ :=
    Finset.single_le_sum (fun j hj => inv_nonneg.mpr (abs_nonneg (a j))) (Finset.mem_univ i)
  refine ⟨hnorm.trans (le_max_left _ _ |>.trans hK.le), ?_⟩
  have hpos : 0 < |a i| := abs_pos.mpr (ha i)
  have hi : (|a i|)⁻¹ < (K : ℝ) + 1 := by
    have hibound := hinv.trans (le_max_right (∑ j, ‖v j‖) (∑ j, (|a j|)⁻¹))
    linarith
  have hmul : (1 : ℝ) < |a i| * ((K : ℝ) + 1) := by
    have h := mul_lt_mul_of_pos_left hi hpos
    simpa only [mul_inv_cancel₀ hpos.ne'] using h
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < K + 1)).mpr hmul.le

end NoUniversalFSigma.TensorSpan

namespace NoUniversalFSigma.TensorSpan

/-- A nonzero square-summable vector has a nonzero coordinate. -/
theorem exists_nonzero_l2_coordinate {I : Type*} (v : L2Coordinates.L2 I) (hv : v ≠ 0) :
    ∃ i, v i ≠ 0 := by
  by_contra h
  push_neg at h
  apply hv
  ext i
  exact h i

end NoUniversalFSigma.TensorSpan
end
end

/- Source module: NoUniversalFSigma.TensorFSigma -/
section
noncomputable section
attribute [local instance] Classical.propDecidable
open Set TopologicalSpace Topology
open scoped BigOperators

namespace NoUniversalFSigma.TensorFamily
open L2Coordinates FiniteL2 TensorSpan

/-- A chart uses only finite coordinate choices, natural bounds and the
countable normalized separating features of the factor families. -/
abbrev TensorChartData (A : ℕ → AdmissibleFamily) :=
  Σ B : Finset ℕ, Σ m : ℕ,
    (Bool → PinData A m) × (Fin m → ℕ) ×
      (Fin m → (B → Option ℕ)) × ℕ

theorem countable_tensorChartData (A : ℕ → AdmissibleFamily) :
    Countable (TensorChartData A) := by
  letI (m : ℕ) : Countable (PinData A m) := countable_pinData A m
  infer_instance

def tensorChartFromData (A : ℕ → AdmissibleFamily)
    (C : ∀ B : Finset ℕ, ℕ → Set (AugmentedPacket B))
    (d : TensorChartData A) : Set Fock :=
  let B := d.1
  let D := d.2.2.1
  if (∀ r, Disjoint (D r).1 B) ∧ Disjoint (D false).1 (D true).1 then
    tensorChart A B D (fun i => C B (d.2.2.2.1 i))
      (fun i => lp.evalCLM ℝ (fun _ : B → Option ℕ => ℝ) 2 (d.2.2.2.2.1 i))
      (1 / ((d.2.2.2.2.2 : ℝ) + 1)) d.2.2.2.2.2
  else ∅

theorem isClosed_tensorChartFromData (A : ℕ → AdmissibleFamily)
    (C : ∀ B : Finset ℕ, ℕ → Set (AugmentedPacket B))
    (hC : ∀ B n, IsClosed (C B n)) (d : TensorChartData A) :
    IsClosed (tensorChartFromData A C d) := by
  rcases d with ⟨B, m, D, a, k, K⟩
  dsimp only [tensorChartFromData]
  split_ifs with h
  · exact isClosed_tensorChart A B D h.1 h.2 (fun i => C B (a i))
      (fun i => hC B (a i)) _ _ _ (by positivity)
  · exact isClosed_empty

theorem tensorChartFromData_subset_span (A : ℕ → AdmissibleFamily)
    (C : ∀ B : Finset ℕ, ℕ → Set (AugmentedPacket B))
    (hC : ∀ B n, C B n ⊆ finiteSpan A B) (d : TensorChartData A) :
    tensorChartFromData A C d ⊆ Submodule.span ℝ (range (family A)) := by
  rcases d with ⟨B, m, D, a, k, K⟩
  dsimp only [tensorChartFromData]
  split_ifs
  · exact tensorChart_subset_span A B D (fun i => C B (a i))
      (fun i => hC B (a i)) _ _ _
  · exact empty_subset _

theorem exists_tensorChartFromData (A : ℕ → AdmissibleFamily)
    (C : ∀ B : Finset ℕ, ℕ → Set (AugmentedPacket B))
    (hC : ∀ B, (finiteSpan A B : Set (AugmentedPacket B)) = ⋃ n, C B n)
    {y : Fock} (hy : y ∈ Submodule.span ℝ (range (family A))) :
    ∃ d : TensorChartData A, y ∈ tensorChartFromData A C d := by
  classical
  obtain ⟨m, B, v, q, hv, hq, hy⟩ := exists_mixed_representation A hy
  have hvC (i : Fin m) : ∃ n, v i ∈ C B n := by
    have hi : v i ∈ (finiteSpan A B : Set (AugmentedPacket B)) := (hv i).1
    rw [hC B] at hi
    exact mem_iUnion.mp hi
  choose a ha using hvC
  choose k hk using fun i => exists_nonzero_l2_coordinate (v i) (hv i).2
  obtain ⟨K, hK⟩ := exists_uniform_chart_bounds v (fun i => v i (k i)) hk
  obtain ⟨D, hWB, hD, hpin⟩ := exists_pinned_tail_data A B q hq
  refine ⟨⟨B, m, D, a, k, K⟩, ?_⟩
  dsimp only [tensorChartFromData]
  rw [if_pos ⟨hWB, hD⟩]
  refine ⟨v, (fun c => fun n : Outside B => q c n), ?_, hpin, ?_⟩
  · intro i
    exact ⟨ha i, (hK i).1, (hK i).2⟩
  · exact hy.symm

/-- The algebraic span of the actual weighted countable tensor family is
F-sigma. This supplies the countable tensor step of the rank construction. -/
theorem isFSigma_span_family (A : ℕ → AdmissibleFamily) :
    IsFSigma (Submodule.span ℝ (range (family A)) : Set Fock) := by
  classical
  choose C hCclosed hC using isFSigma_finiteSpan A
  have hCsub (B : Finset ℕ) (n : ℕ) : C B n ⊆ finiteSpan A B := by
    intro v hv
    rw [hC B]
    exact mem_iUnion.mpr ⟨n, hv⟩
  letI : Countable (TensorChartData A) := countable_tensorChartData A
  obtain ⟨e, he⟩ := exists_surjective_nat (Option (TensorChartData A))
  let chart : Option (TensorChartData A) → Set Fock := fun d =>
    match d with
    | none => ∅
    | some d => tensorChartFromData A C d
  refine ⟨fun n => chart (e n), ?_, ?_⟩
  · intro n
    rcases hd : e n with _ | d
    · simpa only [hd, chart] using (isClosed_empty : IsClosed (∅ : Set Fock))
    · simpa only [hd, chart] using isClosed_tensorChartFromData A C hCclosed d
  · ext y
    constructor
    · intro hy
      obtain ⟨d, hd⟩ := exists_tensorChartFromData A C hC hy
      obtain ⟨n, hn⟩ := he (some d)
      exact mem_iUnion.mpr ⟨n, by simpa only [hn, chart] using hd⟩
    · intro hy
      obtain ⟨n, hn⟩ := mem_iUnion.mp hy
      rcases hd : e n with _ | d
      · simpa only [hd, chart, mem_empty_iff_false] using hn
      · exact tensorChartFromData_subset_span A C hCsub d
          (by simpa only [hd, chart] using hn)

end NoUniversalFSigma.TensorFamily
end
end

universe u

theorem solution
    {Y : Type u} [TopologicalSpace Y] [PolishSpace Y]
    (F : Setoid Y) (hF : NoUniversalFSigma.IsFSigmaRelation F.r) :
    ∃ H : Submodule ℝ NoUniversalFSigma.RealL2,
      NoUniversalFSigma.IsFSigma (H : Set NoUniversalFSigma.RealL2) ∧
      NoUniversalFSigma.IsFSigmaRelation (NoUniversalFSigma.CosetRelation H) ∧
      ¬ ∃ f : NoUniversalFSigma.RealL2 → Y,
        NoUniversalFSigma.IsBaireMeasurable f ∧
          NoUniversalFSigma.IsReduction f (NoUniversalFSigma.CosetRelation H) F.r :=
  NoUniversalFSigma.main_of_rankWitnesses
    (NoUniversalFSigma.rankWitnesses_of_tensorFSigma
      NoUniversalFSigma.TensorFamily.isFSigma_span_family) F hF

#print axioms solution
