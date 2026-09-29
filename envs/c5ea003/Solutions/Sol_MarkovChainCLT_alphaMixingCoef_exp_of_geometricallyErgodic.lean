-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_exp_of_geometricallyErgodic
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T02:34:22.654715+00:00
-- url     : https://prove2.me/submissions/102bae97-b045-4df3-9301-8aaffadc60e1

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_exp_of_geometricallyErgodic_of_countablyGenerated
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_map_pathMap
import Theorems.Thm_MarkovChainCLT_exists_countable_alpha_witnesses

set_option maxHeartbeats 1000000

section
open MeasureTheory ProbabilityTheory Filter Finset Preorder
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

namespace ChainMapScratch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- coordinatewise application on `Π i : Iic b, _`. -/
def mapIic (φ : X → Y) (b : ℕ) (z : Π _i : Iic b, X) : Π _i : Iic b, Y := fun i => φ (z i)

lemma measurable_mapIic {φ : X → Y} (hφ : Measurable φ) (b : ℕ) : Measurable (mapIic φ b) :=
  measurable_pi_lambda _ (fun i => hφ.comp (measurable_pi_apply i))

lemma measurable_mapSeq {φ : X → Y} (hφ : Measurable φ) :
    Measurable (fun (ω : ℕ → X) (i : ℕ) => φ (ω i)) :=
  measurable_pi_lambda _ (fun i => hφ.comp (measurable_pi_apply i))

/-- `Measure.bind` after `map`. -/
lemma bind_map' {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) {f : α → β} (hf : Measurable f) (g : β → Measure γ) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (g ∘ f) := by
  ext s hs
  rw [Measure.bind_apply hs hg.aemeasurable, Measure.bind_apply hs (hg.comp hf).aemeasurable]
  exact lintegral_map ((Measure.measurable_coe hs).comp hg) hf

/-- the one-step claim. -/
lemma partialTraj_succ_self_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y)
    [IsMarkovKernel Q] (φ : X → Y) (hφ : Measurable φ)
    (hPQ : ∀ x, Q (φ x) = (P x).map φ) (b : ℕ) (z : Π _i : Iic b, X) :
    Kernel.partialTraj (X := fun _ : ℕ => Y) (BanditAlgorithm.markovChainStep Q) b (b + 1)
        (mapIic φ b z)
      = (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) b (b + 1) z).map
          (mapIic φ (b + 1)) := by
  rw [Kernel.partialTraj_succ_self, Kernel.partialTraj_succ_self]
  rw [Kernel.map_apply, Kernel.map_apply, Kernel.prod_apply, Kernel.prod_apply, Kernel.id_apply,
    Kernel.id_apply, Kernel.map_apply, Kernel.map_apply,
    Measure.map_map (measurable_mapIic hφ _) measurable_IicProdIoc]
  rotate_left
  · exact (MeasurableEquiv.piSingleton b).measurable
  · exact (MeasurableEquiv.piSingleton b).measurable
  · exact measurable_IicProdIoc
  · exact measurable_IicProdIoc
  set ψ : (Π _i : Ioc b (b + 1), X) → (Π _i : Ioc b (b + 1), Y) := fun w i => φ (w i) with hψ
  have hψm : Measurable ψ := measurable_pi_lambda _ (fun i => hφ.comp (measurable_pi_apply i))
  have hstep : BanditAlgorithm.markovChainStep Q b (mapIic φ b z)
      = (BanditAlgorithm.markovChainStep P b z).map φ := by
    simp only [BanditAlgorithm.markovChainStep, Kernel.comap_apply]
    exact hPQ _
  rw [hstep, Measure.map_map (MeasurableEquiv.piSingleton b).measurable hφ]
  have hnat : (mapIic φ (b + 1)) ∘ (IicProdIoc (X := fun _ : ℕ => X) b (b + 1))
      = (IicProdIoc (X := fun _ : ℕ => Y) b (b + 1)) ∘ (Prod.map (mapIic φ b) ψ) := by
    funext p i
    simp only [Function.comp_apply, mapIic, IicProdIoc_def, Prod.map_fst, Prod.map_snd, hψ]
    split_ifs <;> rfl
  have hsing : (⇑(MeasurableEquiv.piSingleton (X := fun _ : ℕ => Y) b)) ∘ φ
      = ψ ∘ ⇑(MeasurableEquiv.piSingleton (X := fun _ : ℕ => X) b) := by
    funext x i
    obtain ⟨i, hi⟩ := i
    obtain rfl := Nat.mem_Ioc_succ.1 hi
    rfl
  have hdirac : Measure.dirac (mapIic φ b z) = (Measure.dirac z).map (mapIic φ b) :=
    (Measure.map_dirac' (measurable_mapIic hφ b) z).symm
  rw [hsing, ← Measure.map_map hψm (MeasurableEquiv.piSingleton b).measurable, hdirac,
    Measure.map_prod_map _ _ (measurable_mapIic hφ b) hψm, Measure.map_map, hnat]
  · exact measurable_IicProdIoc
  · exact (measurable_mapIic hφ b).prodMap hψm


/-- finite-dimensional claim. -/
lemma partialTraj_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y)
    [IsMarkovKernel Q] (φ : X → Y) (hφ : Measurable φ)
    (hPQ : ∀ x, Q (φ x) = (P x).map φ) {a b : ℕ} (hab : a ≤ b) (z : Π _i : Iic a, X) :
    Kernel.partialTraj (X := fun _ : ℕ => Y) (BanditAlgorithm.markovChainStep Q) a b (mapIic φ a z)
      = (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) a b z).map
          (mapIic φ b) := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Kernel.partialTraj_self, Kernel.partialTraj_self, Kernel.id_apply, Kernel.id_apply,
      Measure.map_dirac' (measurable_mapIic hφ a)]
  | succ k hak ih =>
    rw [Kernel.partialTraj_succ_eq_comp hak, Kernel.partialTraj_succ_eq_comp hak,
      Kernel.comp_apply, Kernel.comp_apply, ih,
      bind_map' _ (measurable_mapIic hφ k) _ (Kernel.measurable _)]
    have hpt : (⇑(Kernel.partialTraj (X := fun _ : ℕ => Y) (BanditAlgorithm.markovChainStep Q) k (k + 1)))
        ∘ (mapIic φ k)
        = fun w => (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k (k + 1) w).map
            (mapIic φ (k + 1)) := by
      funext w
      exact partialTraj_succ_self_map P Q φ hφ hPQ k w
    rw [hpt]
    -- `(μ.bind κ).map f = μ.bind (fun w => (κ w).map f)`
    have := Measure.map_comp
      (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) a k z)
      (Kernel.partialTraj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) k (k + 1))
      (measurable_mapIic hφ (k + 1))
    rw [this]
    congr 1
    funext w
    exact (Kernel.map_apply _ (measurable_mapIic hφ (k + 1)) w).symm

/-- the trajectory law is natural. -/
lemma traj_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y)
    [IsMarkovKernel Q] (φ : X → Y) (hφ : Measurable φ)
    (hPQ : ∀ x, Q (φ x) = (P x).map φ) (z : Π _i : Iic 0, X) :
    Kernel.traj (X := fun _ : ℕ => Y) (BanditAlgorithm.markovChainStep Q) 0 (mapIic φ 0 z)
      = (Kernel.traj (X := fun _ : ℕ => X) (BanditAlgorithm.markovChainStep P) 0 z).map
          (fun ω i => φ (ω i)) := by
  rw [Kernel.traj_apply]
  haveI : ∀ I : Finset ℕ, IsFiniteMeasure (inducedFamily (X := fun _ : ℕ => Y)
      (fun n => (Kernel.partialTraj (X := fun _ : ℕ => Y) (BanditAlgorithm.markovChainStep Q) 0 n)
        (mapIic φ 0 z)) I) := fun I => by
    unfold inducedFamily
    infer_instance
  refine ((Kernel.isProjectiveLimit_trajFun (X := fun _ : ℕ => Y)
    (BanditAlgorithm.markovChainStep Q) 0 (mapIic φ 0 z)).unique ?_)
  rw [isProjectiveLimit_nat_iff
    (Kernel.isProjectiveMeasureFamily_partialTraj (X := fun _ : ℕ => Y)
      (BanditAlgorithm.markovChainStep Q) _)]
  intro n
  rw [inducedFamily_Iic, Measure.map_map (measurable_frestrictLe n) (measurable_mapSeq hφ)]
  have hcomp : (frestrictLe (π := fun _ : ℕ => Y) n) ∘ (fun (ω : ℕ → X) i => φ (ω i))
      = (mapIic φ n) ∘ (frestrictLe (π := fun _ : ℕ => X) n) := by
    funext ω i; rfl
  rw [hcomp, ← Measure.map_map (measurable_mapIic hφ n) (measurable_frestrictLe n),
    Kernel.traj_map_frestrictLe_apply, partialTraj_map P Q φ hφ hPQ (Nat.zero_le n)]

/-- **Functoriality of the chain law.** -/
theorem chainMeasure_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y)
    [IsMarkovKernel Q] (φ : X → Y) (hφ : Measurable φ)
    (hPQ : ∀ x, Q (φ x) = (P x).map φ) (μ : Measure X) :
    chainMeasure Q (μ.map φ) = (chainMeasure P μ).map (fun ω i => φ (ω i)) := by
  simp only [chainMeasure]
  rw [Measure.map_comp _ _ (measurable_mapSeq hφ)]
  show (μ.map φ).bind (BanditAlgorithm.markovChainKernel Q)
    = μ.bind ((BanditAlgorithm.markovChainKernel P).map (fun ω i => φ (ω i)))
  rw [bind_map' _ hφ _ (Kernel.measurable _)]
  congr 1
  funext x
  rw [Function.comp_apply, Kernel.map_apply _ (measurable_mapSeq hφ),
    BanditAlgorithm.markovChainKernel, BanditAlgorithm.markovChainKernel, Kernel.comap_apply,
    Kernel.comap_apply]
  exact traj_map P Q φ hφ hPQ (fun _ => x)

end ChainMapScratch
end

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT ChainMapScratch

namespace ChainMapScratch

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

lemma iterKernel_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y) [IsMarkovKernel Q]
    (φ : X → Y) (hφ : Measurable φ) (hPQ : ∀ x, Q (φ x) = (P x).map φ) (n : ℕ) (x : X) :
    iterKernel Q n (φ x) = (iterKernel P n x).map φ := by
  induction n with
  | zero => rw [iterKernel_zero, iterKernel_zero, Kernel.id_apply, Kernel.id_apply,
      Measure.map_dirac' hφ]
  | succ n ih =>
    rw [iterKernel_succ, iterKernel_succ, Kernel.comp_apply, Kernel.comp_apply, ih,
      bind_map' _ hφ _ (Kernel.measurable _)]
    have h1 : (⇑Q) ∘ φ = fun x => (P x).map φ := by funext x; exact hPQ x
    rw [h1]
    have := Measure.map_comp (iterKernel P n x) P hφ
    rw [this]
    congr 1
    funext y
    exact (Kernel.map_apply _ hφ y).symm

lemma tvDist_map_le (φ : X → Y) (hφ : Measurable φ) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist (μ.map φ) (ν.map φ) ≤ tvDist μ ν := by
  unfold tvDist
  have hbdd : BddAbove {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨A, hA, rfl⟩
    have h1 : (μ A).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h2 : (ν A).toReal ≤ 1 := by
      rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]; constructor <;> linarith
  refine csSup_le_csSup hbdd ⟨_, ∅, MeasurableSet.empty, rfl⟩ ?_
  rintro r ⟨B, hB, rfl⟩
  refine ⟨φ ⁻¹' B, hφ hB, ?_⟩
  rw [Measure.map_apply hφ hB, Measure.map_apply hφ hB]

lemma tvDist_nonneg' (μ ν : Measure X) : 0 ≤ tvDist μ ν := by
  unfold tvDist
  apply Real.sSup_nonneg
  rintro r ⟨A, _, rfl⟩
  exact abs_nonneg _

lemma invariant_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y) [IsMarkovKernel Q]
    (φ : X → Y) (hφ : Measurable φ) (hPQ : ∀ x, Q (φ x) = (P x).map φ) (π : Measure X)
    (hinv : Kernel.Invariant P π) : Kernel.Invariant Q (π.map φ) := by
  unfold Kernel.Invariant at *
  show (π.map φ).bind Q = π.map φ
  rw [bind_map' _ hφ _ (Kernel.measurable _)]
  have h1 : (⇑Q) ∘ φ = fun x => (P x).map φ := by funext x; exact hPQ x
  rw [h1]
  have := Measure.map_comp π P hφ
  have h2 : (⇑(P.map φ)) = fun x => (P x).map φ := by
    funext y; exact Kernel.map_apply _ hφ y
  rw [h2] at this
  rw [← this]
  show ((P ∘ₘ π).map φ) = π.map φ
  rw [hinv]

lemma harrisErgodic_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y) [IsMarkovKernel Q]
    (φ : X → Y) (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (hPQ : ∀ x, Q (φ x) = (P x).map φ) (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) : HarrisErgodic Q (π.map φ) := by
  refine ⟨invariant_map P Q φ hφ hPQ π hP.1, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hsurj y
  refine squeeze_zero (fun n => tvDist_nonneg' _ _) (fun n => ?_) (hP.2 x)
  rw [iterKernel_map P Q φ hφ hPQ]
  exact tvDist_map_le φ hφ _ _

lemma geometricallyErgodic_map (P : Kernel X X) [IsMarkovKernel P] (Q : Kernel Y Y)
    [IsMarkovKernel Q] (φ : X → Y) (hφ : Measurable φ) (hsurj : Function.Surjective φ)
    (hPQ : ∀ x, Q (φ x) = (P x).map φ) (π : Measure X) [IsProbabilityMeasure π]
    (hgeo : GeometricallyErgodic P π) : GeometricallyErgodic Q (π.map φ) := by
  obtain ⟨M, t, hM0, ht0, ht1, hrate⟩ := hgeo
  refine ⟨fun y => M (Function.surjInv hsurj y), t, fun y => hM0 _, ht0, ht1, ?_⟩
  intro y n hn
  have hy : φ (Function.surjInv hsurj y) = y := Function.surjInv_eq hsurj y
  calc tvDist (iterKernel Q n y) (π.map φ)
      = tvDist (iterKernel Q n (φ (Function.surjInv hsurj y))) (π.map φ) := by rw [hy]
    _ ≤ tvDist (iterKernel P n (Function.surjInv hsurj y)) π := by
        rw [iterKernel_map P Q φ hφ hPQ]; exact tvDist_map_le φ hφ _ _
    _ ≤ M (Function.surjInv hsurj y) * t ^ n := hrate _ n hn

end ChainMapScratch
end

section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ProbabilityTheory

namespace ChainMapScratch

variable {X : Type*} [m : MeasurableSpace X]

/-- one closure step -/
def closureStep (P : Kernel X X) (D : Set (Set X)) : Set (Set X) :=
  D ∪ (compl '' D) ∪ (image2 (· ∩ ·) D D) ∪
    ⋃ S ∈ D, range (fun q : ℚ => {x | ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < P x S})

lemma subset_closureStep (P : Kernel X X) (D : Set (Set X)) : D ⊆ closureStep P D := fun S hS =>
  Or.inl (Or.inl (Or.inl hS))

lemma countable_closureStep (P : Kernel X X) {D : Set (Set X)} (hD : D.Countable) :
    (closureStep P D).Countable := by
  refine ((hD.union (hD.image _)).union (hD.image2 hD _)).union ?_
  exact hD.biUnion (fun S _ => countable_range _)

lemma measurableSet_closureStep (P : Kernel X X) {D : Set (Set X)}
    (hD : ∀ S ∈ D, MeasurableSet S) : ∀ S ∈ closureStep P D, MeasurableSet S := by
  rintro S (((hS | ⟨T, hT, rfl⟩) | ⟨T, hT, U, hU, rfl⟩) | hS)
  · exact hD S hS
  · exact (hD T hT).compl
  · exact (hD T hT).inter (hD U hU)
  · simp only [mem_iUnion, mem_range] at hS
    obtain ⟨T, hT, q, rfl⟩ := hS
    exact measurableSet_lt measurable_const (P.measurable_coe (hD T hT))

/-- the levels -/
def levels (P : Kernel X X) (C : Set (Set X)) : ℕ → Set (Set X)
  | 0 => C ∪ {univ}
  | k + 1 => closureStep P (levels P C k)

lemma levels_mono (P : Kernel X X) (C : Set (Set X)) : Monotone (levels P C) :=
  monotone_nat_of_le_succ (fun k => subset_closureStep P _)

lemma countable_levels (P : Kernel X X) {C : Set (Set X)} (hC : C.Countable) (k : ℕ) :
    (levels P C k).Countable := by
  induction k with
  | zero => exact hC.union (countable_singleton _)
  | succ k ih => exact countable_closureStep P ih

lemma measurableSet_levels (P : Kernel X X) {C : Set (Set X)} (hC : ∀ S ∈ C, MeasurableSet S)
    (k : ℕ) : ∀ S ∈ levels P C k, MeasurableSet S := by
  induction k with
  | zero =>
    rintro S (hS | hS)
    · exact hC S hS
    · rw [mem_singleton_iff] at hS; rw [hS]; exact MeasurableSet.univ
  | succ k ih => exact measurableSet_closureStep P ih

/-- the countable generating family -/
def gen (P : Kernel X X) (C : Set (Set X)) : Set (Set X) := ⋃ k, levels P C k

lemma countable_gen (P : Kernel X X) {C : Set (Set X)} (hC : C.Countable) :
    (gen P C).Countable := countable_iUnion (countable_levels P hC)

lemma measurableSet_gen (P : Kernel X X) {C : Set (Set X)} (hC : ∀ S ∈ C, MeasurableSet S) :
    ∀ S ∈ gen P C, MeasurableSet S := by
  intro S hS
  obtain ⟨k, hk⟩ := mem_iUnion.1 hS
  exact measurableSet_levels P hC k S hk

lemma mem_gen_of_mem (P : Kernel X X) (C : Set (Set X)) {S : Set X} (hS : S ∈ C) : S ∈ gen P C :=
  mem_iUnion.2 ⟨0, Or.inl hS⟩

lemma univ_mem_gen (P : Kernel X X) (C : Set (Set X)) : univ ∈ gen P C :=
  mem_iUnion.2 ⟨0, Or.inr (mem_singleton _)⟩

lemma inter_mem_gen (P : Kernel X X) (C : Set (Set X)) {S T : Set X} (hS : S ∈ gen P C)
    (hT : T ∈ gen P C) : S ∩ T ∈ gen P C := by
  obtain ⟨k, hk⟩ := mem_iUnion.1 hS
  obtain ⟨l, hl⟩ := mem_iUnion.1 hT
  refine mem_iUnion.2 ⟨max k l + 1, ?_⟩
  exact Or.inl (Or.inr ⟨S, levels_mono P C (le_max_left k l) hk, T,
    levels_mono P C (le_max_right k l) hl, rfl⟩)

lemma level_set_mem_gen (P : Kernel X X) (C : Set (Set X)) {S : Set X} (hS : S ∈ gen P C)
    (q : ℚ) : {x | ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < P x S} ∈ gen P C := by
  obtain ⟨k, hk⟩ := mem_iUnion.1 hS
  refine mem_iUnion.2 ⟨k + 1, Or.inr ?_⟩
  simp only [mem_iUnion, mem_range]
  exact ⟨S, hk, q, rfl⟩

lemma isPiSystem_gen (P : Kernel X X) (C : Set (Set X)) : IsPiSystem (gen P C) :=
  fun S hS T hT _ => inter_mem_gen P C hS hT

/-- measurability of `x ↦ P x S` w.r.t. `generateFrom (gen P C)` for `S ∈ gen P C`. -/
lemma measurable_kernel_gen (P : Kernel X X) (C : Set (Set X)) {S : Set X} (hS : S ∈ gen P C) :
    @Measurable X ℝ≥0∞ (MeasurableSpace.generateFrom (gen P C)) _ (fun x => P x S) := by
  have key : ∀ a : ℝ≥0∞,
      @MeasurableSet X (MeasurableSpace.generateFrom (gen P C)) ((fun x => P x S) ⁻¹' Ioi a) := by
    intro a
    by_cases ha : a = ⊤
    · have : (fun x => P x S) ⁻¹' Ioi a = ∅ := by
        ext x; simp [ha]
      rw [this]; exact @MeasurableSet.empty X (MeasurableSpace.generateFrom (gen P C))
    · have : (fun x => P x S) ⁻¹' Ioi a =
          ⋃ q ∈ {q : ℚ | a < ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)},
            {x | ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < P x S} := by
        ext x
        simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_setOf_eq, exists_prop]
        constructor
        · intro h
          obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
          exact ⟨q, hq1, hq2⟩
        · rintro ⟨q, hq1, hq2⟩
          exact hq1.trans hq2
      rw [this]
      refine @MeasurableSet.biUnion X ℚ (MeasurableSpace.generateFrom (gen P C)) _ _
        (to_countable _) (fun q _ => ?_)
      exact MeasurableSpace.measurableSet_generateFrom (level_set_mem_gen P C hS q)
  have h1 : @Measurable X ℝ≥0∞ (MeasurableSpace.generateFrom (gen P C))
      (MeasurableSpace.generateFrom (range Ioi)) (fun x => P x S) :=
    @measurable_generateFrom X ℝ≥0∞ (MeasurableSpace.generateFrom (gen P C)) _ _
      (by rintro t ⟨a, rfl⟩; exact key a)
  rwa [← borel_eq_generateFrom_Ioi, ← BorelSpace.measurable_eq] at h1

theorem exists_countablyGenerated_kernel_measurable (P : Kernel X X) [IsMarkovKernel P]
    (C : Set (Set X)) (hC : C.Countable) (hCm : ∀ S ∈ C, MeasurableSet S) :
    ∃ G : MeasurableSpace X, G ≤ m ∧ @MeasurableSpace.CountablyGenerated X G ∧
      (∀ S ∈ C, MeasurableSet[G] S) ∧
      ∀ A, MeasurableSet[G] A → Measurable[G] (fun x => P x A) := by
  have hGm : MeasurableSpace.generateFrom (gen P C) ≤ m :=
    MeasurableSpace.generateFrom_le (measurableSet_gen P hCm)
  refine ⟨MeasurableSpace.generateFrom (gen P C), hGm,
    @MeasurableSpace.CountablyGenerated.mk X (MeasurableSpace.generateFrom (gen P C))
      ⟨gen P C, countable_gen P hC, rfl⟩,
    fun S hS => MeasurableSpace.measurableSet_generateFrom (mem_gen_of_mem P C hS), ?_⟩
  intro A hA
  refine MeasurableSpace.induction_on_inter (m := MeasurableSpace.generateFrom (gen P C))
    (C := fun (t : Set X) (_ : @MeasurableSet X (MeasurableSpace.generateFrom (gen P C)) t) =>
      @Measurable X ℝ≥0∞ (MeasurableSpace.generateFrom (gen P C)) _ (fun x => P x t))
    (s := gen P C) rfl (isPiSystem_gen P C) ?_ ?_ ?_ ?_ A hA
  · simp only [measure_empty]; exact measurable_const
  · intro t ht
    exact measurable_kernel_gen P C ht
  · intro t ht hmeas
    have huniv : @Measurable X ℝ≥0∞ (MeasurableSpace.generateFrom (gen P C)) _
        (fun x => P x univ) :=
      measurable_kernel_gen P C (univ_mem_gen P C)
    have : (fun x => P x tᶜ) = fun x => P x univ - P x t := by
      funext x
      exact measure_compl (hGm _ ht) (measure_ne_top _ _)
    rw [this]
    exact huniv.sub hmeas
  · intro f hdisj hf hmeas
    have : (fun x => P x (⋃ i, f i)) = fun x => ∑' i, P x (f i) := by
      funext x
      exact measure_iUnion hdisj (fun i => hGm _ (hf i))
    rw [this]
    exact Measurable.ennreal_tsum hmeas

end ChainMapScratch
end

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT ChainMapScratch

namespace ChainMapScratch

/- NB: a local `G : MeasurableSpace X` is a local instance; we always declare it *before* the
ambient instance `m` so that `m` wins instance resolution. -/

/-- the kernel `P` viewed on the coarser σ-algebra `G` (via the identity map). -/
noncomputable def restrictKernel {X : Type*} (G : MeasurableSpace X) [m : MeasurableSpace X]
    (P : Kernel X X) (hG : G ≤ m)
    (hPG : ∀ A, MeasurableSet[G] A → Measurable[G] (fun x => P x A)) : @Kernel X X G G :=
  @Kernel.mk X X G G (fun x => @Measure.map X X m G id (P x)) (by
    refine @Measure.measurable_of_measurable_coe X X G G _ (fun s hs => ?_)
    have : (fun x => (@Measure.map X X m G id (P x)) s) = fun x => P x s := by
      funext x
      rw [@Measure.map_apply X X m G (P x) id (measurable_id'' hG) s hs]
      rfl
    rw [this]
    exact hPG s hs)

lemma isMarkovKernel_restrictKernel {X : Type*} (G : MeasurableSpace X) [m : MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (hG : G ≤ m)
    (hPG : ∀ A, MeasurableSet[G] A → Measurable[G] (fun x => P x A)) :
    @IsMarkovKernel X X G G (restrictKernel G P hG hPG) := by
  refine @IsMarkovKernel.mk X X G G _ (fun x => ?_)
  show @IsProbabilityMeasure X G (@Measure.map X X m G id (P x))
  exact @Measure.isProbabilityMeasure_map X X m G (P x) _ id
    (@Measurable.aemeasurable X X m G id (P x) (measurable_id'' hG))

/-- monotonicity of the process σ-algebra in the state σ-algebra. -/
lemma processSigma_mono_state {Ω E : Type*} {m₁ m₂ : MeasurableSpace E} (h : m₁ ≤ m₂)
    (Y : ℕ → Ω → E) (s : Set ℕ) :
    @processSigma Ω E m₁ Y s ≤ @processSigma Ω E m₂ Y s := by
  unfold processSigma
  exact iSup₂_mono (fun i _ => MeasurableSpace.comap_mono h)

theorem alphaExp_aux {X : Type*} (G : MeasurableSpace X) [m : MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π)
    (hGm : G ≤ m) (hGcg : @MeasurableSpace.CountablyGenerated X G)
    (hPG : ∀ A, MeasurableSet[G] A → Measurable[G] (fun x => P x A))
    (𝒞 : Set (Set X)) (h𝒞G : ∀ S ∈ 𝒞, MeasurableSet[G] S) (K : ℕ → ℕ) (A B : ℕ → Set (ℕ → X))
    (hA : ∀ n, MeasurableSet[@processSigma (ℕ → X) X (MeasurableSpace.generateFrom 𝒞)
      (fun i (ω : ℕ → X) => ω i) (Set.Iic (K n))] (A n))
    (hB : ∀ n, MeasurableSet[@processSigma (ℕ → X) X (MeasurableSpace.generateFrom 𝒞)
      (fun i (ω : ℕ → X) => ω i) (Set.Ici (K n + n))] (B n))
    (hbound : ∀ n, alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤
      2 * |((chainMeasure P π) (A n ∩ B n)).toReal -
        ((chainMeasure P π) (A n)).toReal * ((chainMeasure P π) (B n)).toReal|) :
    ∃ c a : ℝ, 0 ≤ c ∧ 0 ≤ a ∧ a < 1 ∧
      ∀ n : ℕ, alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ c * a ^ n := by
  have hgen : MeasurableSpace.generateFrom 𝒞 ≤ G := MeasurableSpace.generateFrom_le h𝒞G
  -- the restricted chain
  let Q : @Kernel X X G G := restrictKernel G P hGm hPG
  have hQ : @IsMarkovKernel X X G G Q := isMarkovKernel_restrictKernel G P hGm hPG
  let ν : @Measure X G := @Measure.map X X m G id π
  have hν : @IsProbabilityMeasure X G ν :=
    @Measure.isProbabilityMeasure_map X X m G π _ id
      (@Measurable.aemeasurable X X m G id π (measurable_id'' hGm))
  have hid : @Measurable X X m G id := measurable_id'' hGm
  have hPν : @HarrisErgodic X G Q ν :=
    @harrisErgodic_map X X m G P _ Q hQ id hid Function.surjective_id (fun x => rfl) π _ hP
  have hgeoν : @GeometricallyErgodic X G Q ν :=
    @geometricallyErgodic_map X X m G P _ Q hQ id hid Function.surjective_id (fun x => rfl) π _
      hgeo
  -- the countably generated case
  obtain ⟨c, a, hc0, ha0, ha1, hα⟩ :=
    @alphaMixingCoef_exp_of_geometricallyErgodic_of_countablyGenerated X G hGcg Q hQ ν hν hPν hgeoν
  -- transport back to `chainMeasure P π`
  have hchain : @chainMeasure X G Q hQ ν
      = @Measure.map (ℕ → X) (ℕ → X) (MeasurableSpace.pi) (@MeasurableSpace.pi ℕ (fun _ => X) fun _ => G)
          (fun ω i => id (ω i)) (chainMeasure P π) :=
    @chainMeasure_map X X m G P _ Q hQ id hid (fun x => rfl) π
  have hpath := fun n => @alphaMixingCoef_map_pathMap (ℕ → X) X _ G (chainMeasure P π)
    (fun i (ω : ℕ → X) => ω i) (fun i => hid.comp (measurable_pi_apply i)) n
  have hαG : ∀ n, @alphaMixingCoef (ℕ → X) X _ G (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n
      ≤ c * a ^ n := by
    intro n
    rw [hpath n]
    have := hα n
    rw [hchain] at this
    exact this
  -- the witnesses are `G`-measurable, so they are dominated by the `G`-coefficient
  refine ⟨2 * c, a, by linarith, ha0, ha1, fun n => ?_⟩
  have hbdd : BddAbove {r | ∃ k : ℕ, ∃ A' B' : Set (ℕ → X),
      MeasurableSet[@processSigma (ℕ → X) X G (fun i (ω : ℕ → X) => ω i) (Set.Iic k)] A' ∧
      MeasurableSet[@processSigma (ℕ → X) X G (fun i (ω : ℕ → X) => ω i) (Set.Ici (k + n))] B' ∧
      r = |((chainMeasure P π) (A' ∩ B')).toReal -
        ((chainMeasure P π) A').toReal * ((chainMeasure P π) B').toReal|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨k, A', B', _, _, rfl⟩
    have hb : ∀ s : Set (ℕ → X), ((chainMeasure P π) s).toReal ≤ 1 := by
      intro s
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
    have h1 := hb (A' ∩ B')
    have h2 := hb A'
    have h3 := hb B'
    have n1 : (0:ℝ) ≤ ((chainMeasure P π) (A' ∩ B')).toReal := ENNReal.toReal_nonneg
    have n2 : (0:ℝ) ≤ ((chainMeasure P π) A').toReal := ENNReal.toReal_nonneg
    have n3 : (0:ℝ) ≤ ((chainMeasure P π) B').toReal := ENNReal.toReal_nonneg
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  have hmem : |((chainMeasure P π) (A n ∩ B n)).toReal -
      ((chainMeasure P π) (A n)).toReal * ((chainMeasure P π) (B n)).toReal|
      ≤ @alphaMixingCoef (ℕ → X) X _ G (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n := by
    unfold alphaMixingCoef
    refine le_csSup hbdd ⟨K n, A n, B n, ?_, ?_, rfl⟩
    · exact processSigma_mono_state hgen _ _ _ (hA n)
    · exact processSigma_mono_state hgen _ _ _ (hB n)
  calc alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n
      ≤ 2 * |((chainMeasure P π) (A n ∩ B n)).toReal -
          ((chainMeasure P π) (A n)).toReal * ((chainMeasure P π) (B n)).toReal| := hbound n
    _ ≤ 2 * (c * a ^ n) := by
        have := hmem.trans (hαG n)
        linarith
    _ = 2 * c * a ^ n := by ring

theorem alphaExp_general {X : Type*} [m : MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ c a : ℝ, 0 ≤ c ∧ 0 ≤ a ∧ a < 1 ∧
      ∀ n : ℕ, alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ c * a ^ n := by
  obtain ⟨𝒞, K, A, B, h𝒞c, h𝒞m, hA, hB, hbound⟩ :=
    exists_countable_alpha_witnesses (chainMeasure P π) (fun i (ω : ℕ → X) => ω i)
  obtain ⟨G, hGm, hGcg, h𝒞G, hPG⟩ := exists_countablyGenerated_kernel_measurable P 𝒞 h𝒞c h𝒞m
  exact @alphaExp_aux X G m P _ π _ hP hgeo hGm hGcg hPG 𝒞 h𝒞G K A B hA hB hbound

end ChainMapScratch
end

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT ChainMapScratch

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ c a : ℝ, 0 ≤ c ∧ 0 ≤ a ∧ a < 1 ∧
      ∀ n : ℕ, alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ c * a ^ n :=
  alphaExp_general P π hP hgeo
