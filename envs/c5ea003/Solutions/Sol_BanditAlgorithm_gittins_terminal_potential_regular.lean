-- Prove2me | solution 1 for BanditAlgorithm.gittins_terminal_potential_regular
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:10:22.562196+00:00
-- url     : https://prove2.me/submissions/4bcbe65f-d7d4-4b55-8f58-af7827896a86

import Definitions.Def_GittinsChargeInterleaving
import Definitions.Def_GittinsFiniteRetirementValue
import Definitions.Def_GittinsIndex
import Definitions.Def_MarkovChainKernel
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.Bounded
import Theorems.Thm_BanditAlgorithm_gittinsFiniteRetirementValue_mono_of_integrable
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_bellman_of_finite_tendsto
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_iff_index_le
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_lipschitz_charge
import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_one_bounds
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_measurable_gittinsFiniteRetirementValue
import Theorems.Thm_BanditAlgorithm_measurable_gittinsRetirementValue_of_finite_tendsto


import Definitions.Def_GittinsTerminalPotential
import Definitions.Def_GittinsPrevailingChargeValue
open MeasureTheory ProbabilityTheory
open Filter Topology

namespace BanditAlgorithm

noncomputable def finiteRetirementTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) :
    ℕ → ℕ → (ℕ → S) → ℕ
  | _, 0, _ => 0
  | b, n + 1, ω =>
      if 0 < r (ω b) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
      then 1 + finiteRetirementTime P r α γ (b + 1) n ω
      else 0

noncomputable def finiteRetirementSegment
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ j ∈ Finset.range m, α ^ j * q (ω (b + j))

lemma finiteRetirementSegment_succ
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) :
    finiteRetirementSegment α q b (m + 1) ω =
      q (ω b) + α * finiteRetirementSegment α q (b + 1) m ω := by
  rw [finiteRetirementSegment, finiteRetirementSegment]
  simp only [Finset.sum_range_succ']
  simp only [pow_zero, one_mul]
  have htail :
      (∑ k ∈ Finset.range m,
        α ^ (k + 1) * q (ω (b + (k + 1)))) =
        α * ∑ j ∈ Finset.range m, α ^ j * q (ω (b + 1 + j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [pow_succ]
    ring_nf
  rw [htail]
  simp [add_comm]

lemma measurable_finiteRetirementTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) :
    ∀ b n, Measurable (finiteRetirementTime P r α γ b n) := by
  intro b n
  induction n generalizing b with
  | zero =>
      simp [finiteRetirementTime]
  | succ n ih =>
      have hv :=
        measurable_gittinsFiniteRetirementValue P hr α γ n
      have hcont : Measurable (fun x ↦
          r x - γ +
            α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x) := by
        exact (hr.sub measurable_const).add
          (measurable_const.mul
            hv.stronglyMeasurable.integral_kernel.measurable)
      rw [show finiteRetirementTime P r α γ b (n + 1) =
          fun ω ↦
            if 0 < r (ω b) - γ +
                α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
            then 1 + finiteRetirementTime P r α γ (b + 1) n ω
            else 0 by rfl]
      apply Measurable.ite
      · exact measurableSet_lt measurable_const
          (hcont.comp (measurable_pi_apply b))
      · fun_prop
      · exact measurable_const

private lemma measurable_trajectory_eval_le
    {S : Type*} [MeasurableSpace S] {b N : ℕ} (hbN : b ≤ N) :
    Measurable[trajectoryFiltration S N] (fun ω : ℕ → S ↦ ω b) := by
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
    Filtration.piLE (X := fun _ : ℕ ↦ S)
  have hadapt :
      Adapted ℱ (fun t (ω : ℕ → S) ↦ ω t) := by
    intro t
    dsimp [ℱ]
    rw [Filtration.piLE_eq_comap_frestrictLe]
    change Measurable[MeasurableSpace.comap
      (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1) inferInstance]
        ((fun z : (i : Finset.Iic t) → S ↦
            z ⟨t, Finset.mem_Iic.2 le_rfl⟩) ∘
          (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1))
    exact (measurable_pi_apply _).comp (comap_measurable _)
  have hmeas : Measurable[ℱ N] (fun ω : ℕ → S ↦ ω b) :=
    hadapt.measurable_le hbN
  have hfil : ℱ N = trajectoryFiltration S N := by
    dsimp [ℱ, trajectoryFiltration]
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rfl
  rwa [hfil] at hmeas

lemma measurableSet_finiteRetirementTime_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) :
    ∀ b n m,
      MeasurableSet[trajectoryFiltration S (b + m)]
        {ω | finiteRetirementTime P r α γ b n ω ≤ m} := by
  intro b n
  induction n generalizing b with
  | zero =>
      intro m
      convert MeasurableSet.univ
      ext ω
      simp [finiteRetirementTime]
  | succ n ih =>
      intro m
      let c : S → ℝ := fun x ↦
        r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x
      have hc : Measurable c := by
        exact (hr.sub measurable_const).add
          (measurable_const.mul
            ((measurable_gittinsFiniteRetirementValue P hr α γ n).stronglyMeasurable
              |>.integral_kernel.measurable))
      cases m with
      | zero =>
          have heval :
              Measurable[trajectoryFiltration S (b + 0)]
                (fun ω : ℕ → S ↦ c (ω b)) :=
            hc.comp (measurable_trajectory_eval_le (by omega))
          have hpos :
              MeasurableSet[trajectoryFiltration S (b + 0)]
                {ω : ℕ → S | 0 < c (ω b)} :=
            measurableSet_lt measurable_const heval
          convert hpos.compl using 1
          ext ω
          simp [finiteRetirementTime, c]
      | succ m =>
          have heval :
              Measurable[trajectoryFiltration S (b + (m + 1))]
                (fun ω : ℕ → S ↦ c (ω b)) :=
            hc.comp (measurable_trajectory_eval_le (by omega))
          have hpos :
              MeasurableSet[trajectoryFiltration S (b + (m + 1))]
                {ω : ℕ → S | 0 < c (ω b)} :=
            measurableSet_lt measurable_const heval
          have hrec :
              MeasurableSet[trajectoryFiltration S (b + (m + 1))]
                {ω |
                  finiteRetirementTime P r α γ (b + 1) n ω ≤ m} := by
            have heq : b + 1 + m = b + (m + 1) := by omega
            rw [← heq]
            exact ih (b + 1) m
          have hset :
              {ω | finiteRetirementTime P r α γ b (n + 1) ω ≤ m + 1} =
                {ω : ℕ → S | 0 < c (ω b)}ᶜ ∪
                  ({ω : ℕ → S | 0 < c (ω b)} ∩
                    {ω |
                      finiteRetirementTime P r α γ (b + 1) n ω ≤ m}) := by
            ext ω
            simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
              Set.mem_inter_iff]
            rw [show finiteRetirementTime P r α γ b (n + 1) ω =
                if 0 < c (ω b) then
                  1 + finiteRetirementTime P r α γ (b + 1) n ω
                else 0 by rfl]
            by_cases hp : 0 < c (ω b)
            · simp [hp]
              omega
            · simp [hp]
          rw [hset]
          exact hpos.compl.union (hpos.inter hrec)

lemma finiteRetirementTime_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) :
    ∀ b n ω, finiteRetirementTime P r α γ b n ω ≤ n := by
  intro b n
  induction n generalizing b with
  | zero =>
      intro ω
      simp [finiteRetirementTime]
  | succ n ih =>
      intro ω
      rw [show finiteRetirementTime P r α γ b (n + 1) ω =
          if 0 < r (ω b) - γ +
              α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
          then 1 + finiteRetirementTime P r α γ (b + 1) n ω
          else 0 by rfl]
      split_ifs
      · simpa [Nat.add_comm] using
          Nat.add_le_add_left (ih (b + 1) ω) 1
      · exact Nat.zero_le _

lemma finiteRetirementSegment_time_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (b n : ℕ) (ω : ℕ → S) :
    finiteRetirementSegment α (fun x ↦ r x - γ) b
        (finiteRetirementTime P r α γ b (n + 1) ω) ω =
      if 0 < r (ω b) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
      then
        r (ω b) - γ +
          α * finiteRetirementSegment α (fun x ↦ r x - γ) (b + 1)
            (finiteRetirementTime P r α γ (b + 1) n ω) ω
      else 0 := by
  rw [show finiteRetirementTime P r α γ b (n + 1) ω =
      if 0 < r (ω b) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω b)
      then 1 + finiteRetirementTime P r α γ (b + 1) n ω
      else 0 by rfl]
  split_ifs with h
  · rw [show 1 + finiteRetirementTime P r α γ (b + 1) n ω =
        finiteRetirementTime P r α γ (b + 1) n ω + 1 by omega]
    rw [finiteRetirementSegment_succ]
  · simp [finiteRetirementSegment]

private lemma updateFinset_apply_of_lt
    {S : Type*} (ω : ℕ → S) {b i : ℕ} (hbi : b < i)
    (x₀ : (j : Finset.Iic b) → S) :
    Function.updateFinset ω (Finset.Iic b) x₀ i = ω i := by
  unfold Function.updateFinset
  split_ifs with hi
  · have hib : i ≤ b := Finset.mem_Iic.mp hi
    omega
  · rfl

private lemma finiteRetirementTime_updateFinset_before
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (ω : ℕ → S) {b c n : ℕ} (hbc : b < c)
    (x₀ : (j : Finset.Iic b) → S) :
    finiteRetirementTime P r α γ c n
        (Function.updateFinset ω (Finset.Iic b) x₀) =
      finiteRetirementTime P r α γ c n ω := by
  induction n generalizing c with
  | zero =>
      simp [finiteRetirementTime]
  | succ n ih =>
      rw [show finiteRetirementTime P r α γ c (n + 1)
            (Function.updateFinset ω (Finset.Iic b) x₀) =
          if 0 < r ((Function.updateFinset ω (Finset.Iic b) x₀) c) - γ +
              α * ∫ y, gittinsFiniteRetirementValue P r α γ n y
                ∂P ((Function.updateFinset ω (Finset.Iic b) x₀) c)
          then 1 + finiteRetirementTime P r α γ (c + 1) n
            (Function.updateFinset ω (Finset.Iic b) x₀)
          else 0 by rfl]
      rw [show finiteRetirementTime P r α γ c (n + 1) ω =
          if 0 < r (ω c) - γ +
              α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω c)
          then 1 + finiteRetirementTime P r α γ (c + 1) n ω
          else 0 by rfl]
      rw [updateFinset_apply_of_lt ω hbc x₀]
      by_cases hc : 0 < r (ω c) - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P (ω c)
      · rw [if_pos hc, if_pos hc]
        exact congrArg (fun z ↦ 1 + z)
          (ih (c := c + 1) (by omega))
      · rw [if_neg hc, if_neg hc]

private lemma finiteRetirementSegment_updateFinset_before
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (ω : ℕ → S) {b c m : ℕ} (hbc : b < c)
    (x₀ : (j : Finset.Iic b) → S) :
    finiteRetirementSegment α q c m
        (Function.updateFinset ω (Finset.Iic b) x₀) =
      finiteRetirementSegment α q c m ω := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [updateFinset_apply_of_lt]
  omega

private lemma integral_partialTraj_succ_current
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : StronglyMeasurable f)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ (x : (j : Finset.Iic (b + 1)) → S),
        f (x ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩)
        ∂Kernel.partialTraj (X := fun _ : ℕ ↦ S)
          (markovChainStep P) b (b + 1) x₀) =
      ∫ y, f y ∂P (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  let e : ((j : Finset.Iic (b + 1)) → S) → S :=
    fun x ↦ x ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩
  have hmapK :=
    Kernel.map_partialTraj_succ_self
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P) b
  have hmap :=
    congrArg
      (fun K : Kernel ((j : Finset.Iic b) → S) S ↦ K x₀)
      hmapK
  dsimp only at hmap
  rw [Kernel.map_apply _ (by fun_prop)] at hmap
  rw [← MeasureTheory.integral_map_of_stronglyMeasurable
    (by fun_prop : Measurable e) hf]
  rw [hmap]
  rfl

noncomputable def finiteRetirementPayoff
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (b n : ℕ) (ω : ℕ → S) : ℝ :=
  finiteRetirementSegment α (fun x ↦ r x - γ) b
    (finiteRetirementTime P r α γ b n ω) ω

lemma discountedStoppedSum_coe_nat
    {S : Type*} (α : ℝ) (f : S → ℝ)
    (m : (ℕ → S) → ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun z ↦ (m z : ℕ∞)) ω =
      finiteRetirementSegment α f 0 (m ω) ω := by
  rw [discountedStoppedSum, finiteRetirementSegment,
    tsum_eq_sum (s := Finset.range (m ω))]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_range] at ht
    simp [ht]
  · intro t ht
    simp only [Finset.mem_range, not_lt] at ht
    simp [not_lt_of_ge ht]

private lemma sum_range_ite_lt
    {m n : ℕ} (hmn : m ≤ n) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range n, if j < m then f j else 0) =
      ∑ j ∈ Finset.range m, f j := by
  symm
  calc
    (∑ j ∈ Finset.range m, f j) =
        ∑ j ∈ Finset.range m, if j < m then f j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_range] at hj
          simp [hj]
    _ = ∑ j ∈ Finset.range n, if j < m then f j else 0 := by
      apply Finset.sum_subset (Finset.range_mono hmn)
      intro j hjn hjm
      simp only [Finset.mem_range, not_lt] at hjm
      simp [hjm]

lemma finiteRetirementPayoff_eq_sum_range
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (b n : ℕ) (ω : ℕ → S) :
    finiteRetirementPayoff P r α γ b n ω =
      ∑ j ∈ Finset.range n,
        if j < finiteRetirementTime P r α γ b n ω then
          α ^ j * (r (ω (b + j)) - γ)
        else 0 := by
  rw [finiteRetirementPayoff, finiteRetirementSegment]
  exact (sum_range_ite_lt
    (finiteRetirementTime_le P r α γ b n ω)
    (fun j ↦ α ^ j * (r (ω (b + j)) - γ))).symm

lemma integrable_finiteRetirementPayoff
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) (b n : ℕ)
    (μ : Measure (ℕ → S))
    [IsFiniteMeasure μ]
    (hcoord : ∀ j < n, Integrable (fun ω ↦ r (ω (b + j))) μ) :
    Integrable (finiteRetirementPayoff P r α γ b n) μ := by
  rw [show finiteRetirementPayoff P r α γ b n =
      fun ω ↦ ∑ j ∈ Finset.range n,
        if j < finiteRetirementTime P r α γ b n ω then
          α ^ j * (r (ω (b + j)) - γ)
        else 0 by
          funext ω
          exact finiteRetirementPayoff_eq_sum_range P r α γ b n ω]
  apply integrable_finset_sum
  intro j hj
  have hset : MeasurableSet
      {ω : ℕ → S | j < finiteRetirementTime P r α γ b n ω} :=
    measurableSet_lt measurable_const
      (measurable_finiteRetirementTime P hr α γ b n)
  have hterm : Integrable
      (fun ω : ℕ → S ↦ α ^ j * (r (ω (b + j)) - γ)) μ :=
    ((hcoord j (Finset.mem_range.1 hj)).sub
      (integrable_const γ)).const_mul (α ^ j)
  rw [show (fun ω : ℕ → S ↦
      if j < finiteRetirementTime P r α γ b n ω then
        α ^ j * (r (ω (b + j)) - γ)
      else 0) =
      {ω : ℕ → S | j < finiteRetirementTime P r α γ b n ω}.indicator
        (fun ω ↦ α ^ j * (r (ω (b + j)) - γ)) by
          funext ω
          simp only [Set.indicator, Set.mem_setOf_eq, Pi.zero_apply]]
  exact hterm.indicator hset

lemma integrable_finiteRetirementSegment_random
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) (m : (ℕ → S) → ℕ) (N : ℕ)
    (hlt : ∀ j, MeasurableSet {ω : ℕ → S | j < m ω})
    (hmN : ∀ ω, m ω ≤ N)
    (μ : Measure (ℕ → S)) [IsFiniteMeasure μ]
    (hcoord : ∀ j < N, Integrable (fun ω ↦ r (ω j)) μ) :
    Integrable
      (fun ω ↦ finiteRetirementSegment α (fun z ↦ r z - γ) 0 (m ω) ω)
      μ := by
  rw [show (fun ω ↦
      finiteRetirementSegment α (fun z ↦ r z - γ) 0 (m ω) ω) =
      fun ω ↦ ∑ j ∈ Finset.range N,
        if j < m ω then α ^ j * (r (ω j) - γ) else 0 by
          funext ω
          rw [finiteRetirementSegment]
          simpa using (sum_range_ite_lt (hmN ω)
            (fun j ↦ α ^ j * (r (ω (0 + j)) - γ))).symm]
  apply integrable_finsetSum
  intro j hj
  have hjN : j < N := Finset.mem_range.1 hj
  have hset : MeasurableSet {ω : ℕ → S | j < m ω} := hlt j
  have hterm : Integrable
      (fun ω : ℕ → S ↦ α ^ j * (r (ω j) - γ)) μ :=
    ((hcoord j hjN).sub (integrable_const γ)).const_mul (α ^ j)
  rw [show (fun ω : ℕ → S ↦
      if j < m ω then α ^ j * (r (ω j) - γ) else 0) =
      {ω : ℕ → S | j < m ω}.indicator
        (fun ω ↦ α ^ j * (r (ω j) - γ)) by
          funext ω
          simp only [Set.indicator, Set.mem_setOf_eq]]
  exact hterm.indicator hset

lemma discountedStoppedSum_finiteRetirementForcedTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦
          ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω =
      r (ω 0) - γ +
        α * finiteRetirementPayoff P r α γ 1 n ω := by
  rw [discountedStoppedSum_coe_nat]
  rw [show 1 + finiteRetirementTime P r α γ 1 n ω =
      finiteRetirementTime P r α γ 1 n ω + 1 by omega]
  rw [finiteRetirementSegment_succ]
  rfl

lemma markovChainMeasure_eq_traj_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x =
      Kernel.traj (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦ x) := by
  rw [← markovChainKernel_apply, markovChainKernel, Kernel.comap_apply]

set_option maxHeartbeats 800000 in
theorem integral_finiteRetirementPayoff
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (hpay : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ b n)
        (Kernel.traj (markovChainStep P) b x₀))
    (hpaySucc : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
        (Kernel.traj (markovChainStep P) b x₀)) :
    ∀ b n (x₀ : (j : Finset.Iic b) → S),
      (∫ ω, finiteRetirementPayoff P r α γ b n ω
          ∂Kernel.traj (markovChainStep P) b x₀) =
        gittinsFiniteRetirementValue P r α γ n
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  intro b n
  induction n generalizing b with
  | zero =>
      intro x₀
      simp [finiteRetirementPayoff, finiteRetirementTime,
        finiteRetirementSegment, gittinsFiniteRetirementValue]
  | succ n ih =>
      intro x₀
      let x : S := x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩
      let c : ℝ :=
        r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x
      have hfix :
          (∫ ω, finiteRetirementPayoff P r α γ b (n + 1) ω
              ∂Kernel.traj (markovChainStep P) b x₀) =
            ∫ ω,
              finiteRetirementPayoff P r α γ b (n + 1)
                (Function.updateFinset ω (Finset.Iic b) x₀)
              ∂Kernel.traj (markovChainStep P) b x₀ :=
        Kernel.integral_traj
          (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
          x₀ (hpay b (n + 1) x₀).1
      rw [hfix]
      by_cases hc : 0 < c
      · have hpath :
            (fun ω ↦
              finiteRetirementPayoff P r α γ b (n + 1)
                (Function.updateFinset ω (Finset.Iic b) x₀)) =
              fun ω ↦
                r x - γ +
                  α * finiteRetirementPayoff P r α γ (b + 1) n ω := by
          funext ω
          rw [finiteRetirementPayoff,
            finiteRetirementSegment_time_succ]
          have hxb :
              Function.updateFinset ω (Finset.Iic b) x₀ b = x := by
            simp [Function.updateFinset, x]
          rw [hxb]
          rw [if_pos hc]
          rw [finiteRetirementPayoff]
          rw [finiteRetirementTime_updateFinset_before
            P r α γ ω (by omega) x₀]
          rw [finiteRetirementSegment_updateFinset_before
            α (fun z ↦ r z - γ) ω (by omega) x₀]
        rw [hpath]
        rw [integral_add
          (integrable_const (r x - γ))
          ((hpaySucc b n x₀).const_mul α)]
        rw [integral_const_mul]
        have hdecomp :=
          Kernel.integral_traj_partialTraj
            (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
            (Nat.le_succ b)
            (hpaySucc b n x₀)
        have hchild :
            (∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
                ∂Kernel.traj (markovChainStep P) b x₀) =
              ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x := by
          rw [← hdecomp]
          have hinner :
              (fun z : (j : Finset.Iic (b + 1)) → S ↦
                ∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
                  ∂Kernel.traj (markovChainStep P) (b + 1) z) =
                fun z ↦
                  gittinsFiniteRetirementValue P r α γ n
                    (z ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩) := by
            funext z
            exact ih (b + 1) z
          rw [hinner]
          exact integral_partialTraj_succ_current P
            (gittinsFiniteRetirementValue P r α γ n)
            (measurable_gittinsFiniteRetirementValue P hr α γ n).stronglyMeasurable
            b x₀
        rw [hchild]
        simpa [gittinsFiniteRetirementValue, x, c] using
          (max_eq_right hc.le).symm
      · have hpath :
            (fun ω ↦
              finiteRetirementPayoff P r α γ b (n + 1)
                (Function.updateFinset ω (Finset.Iic b) x₀)) =
              fun _ ↦ 0 := by
          funext ω
          rw [finiteRetirementPayoff,
            finiteRetirementSegment_time_succ]
          have hxb :
              Function.updateFinset ω (Finset.Iic b) x₀ b = x := by
            simp [Function.updateFinset, x]
          rw [hxb]
          rw [if_neg hc]
        rw [hpath]
        have hc' : c ≤ 0 := le_of_not_gt hc
        simpa [gittinsFiniteRetirementValue, x, c] using hc'

theorem integral_finiteRetirementPayoff_next
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (hpay : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ b n)
        (Kernel.traj (markovChainStep P) b x₀))
    (hpaySucc : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
        (Kernel.traj (markovChainStep P) b x₀))
    (b n : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫ y, gittinsFiniteRetirementValue P r α γ n y
        ∂P (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  have hdecomp :=
    Kernel.integral_traj_partialTraj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      (Nat.le_succ b)
      (hpaySucc b n x₀)
  rw [← hdecomp]
  have hinner :
      (fun z : (j : Finset.Iic (b + 1)) → S ↦
        ∫ ω, finiteRetirementPayoff P r α γ (b + 1) n ω
          ∂Kernel.traj (markovChainStep P) (b + 1) z) =
        fun z ↦
          gittinsFiniteRetirementValue P r α γ n
            (z ⟨b + 1, Finset.mem_Iic.2 le_rfl⟩) := by
    funext z
    exact integral_finiteRetirementPayoff P hr α γ hpay hpaySucc
      (b + 1) n z
  rw [hinner]
  exact integral_partialTraj_succ_current P
    (gittinsFiniteRetirementValue P r α γ n)
    (measurable_gittinsFiniteRetirementValue P hr α γ n).stronglyMeasurable
    b x₀

theorem integral_discountedStoppedSum_finiteRetirementForcedTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) (α γ : ℝ)
    (hpay : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ b n)
        (Kernel.traj (markovChainStep P) b x₀))
    (hpaySucc : ∀ b n (x₀ : (j : Finset.Iic b) → S),
      Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
        (Kernel.traj (markovChainStep P) b x₀))
    (n : ℕ) (x : S) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦
          ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω
        ∂markovChainMeasure P x) =
      r x - γ +
        α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x := by
  rw [markovChainMeasure_eq_traj_zero]
  rw [show (fun ω ↦ discountedStoppedSum α (fun y ↦ r y - γ)
      (fun ω ↦
        ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω) =
      fun ω ↦ r (ω 0) - γ +
        α * finiteRetirementPayoff P r α γ 1 n ω by
          funext ω
          exact discountedStoppedSum_finiteRetirementForcedTime
            P r α γ n ω]
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hr0 : Measurable (fun ω : ℕ → S ↦ r (ω 0)) :=
    hr.comp (measurable_pi_apply 0)
  have hsm :
      AEStronglyMeasurable
        (fun ω : ℕ → S ↦
          r (ω 0) - γ +
            α * finiteRetirementPayoff P r α γ 1 n ω)
        (Kernel.traj (markovChainStep P) 0 x₀) :=
    (hr0.aestronglyMeasurable.sub aestronglyMeasurable_const).add
      ((hpaySucc 0 n x₀).1.const_mul α)
  rw [Kernel.integral_traj
    (X := fun _ : ℕ ↦ S) (κ := markovChainStep P) x₀ hsm]
  have hupdated :
      (fun ω : ℕ → S ↦
        r ((Function.updateFinset ω (Finset.Iic 0) x₀) 0) - γ +
          α * finiteRetirementPayoff P r α γ 1 n
            (Function.updateFinset ω (Finset.Iic 0) x₀)) =
        fun ω ↦
          r x - γ + α * finiteRetirementPayoff P r α γ 1 n ω := by
    funext ω
    have hpayoff :
        finiteRetirementPayoff P r α γ 1 n
            (Function.updateFinset ω (Finset.Iic 0) x₀) =
          finiteRetirementPayoff P r α γ 1 n ω := by
      rw [finiteRetirementPayoff]
      rw [finiteRetirementTime_updateFinset_before
        P r α γ ω (by omega : 0 < 1) x₀]
      rw [finiteRetirementSegment_updateFinset_before
        α (fun z ↦ r z - γ) ω (by omega : 0 < 1) x₀]
      rfl
    rw [hpayoff]
    simp [Function.updateFinset, x₀]
  rw [hupdated]
  rw [integral_add (integrable_const (r x - γ))
    ((hpaySucc 0 n x₀).const_mul α)]
  rw [integral_const_mul]
  rw [integral_finiteRetirementPayoff_next P hr α γ hpay hpaySucc
    0 n x₀]
  simp [x₀]

noncomputable def trajectoryStateMarginal
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) : Measure S :=
  (Kernel.partialTraj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b (b + t) x₀).map
    (fun z ↦ z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩)

lemma trajectoryStateMarginal_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b 0 x₀ =
      Measure.dirac (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  simp only [trajectoryStateMarginal, Nat.add_zero,
    Kernel.partialTraj_self, Kernel.id_apply]
  rw [Measure.map_dirac' (by fun_prop)]

private lemma map_bind_kernel
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → B) (hf : Measurable f)
    (K : Kernel B C) :
    (μ.map f).bind K = μ.bind (fun x ↦ K (f x)) := by
  rw [Measure.bind, Measure.bind, Measure.map_map]
  · rfl
  · exact K.measurable
  · exact hf

lemma trajectoryStateMarginal_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b (t + 1) x₀ =
      (trajectoryStateMarginal P b t x₀).bind P := by
  rw [trajectoryStateMarginal, trajectoryStateMarginal]
  simp only [Nat.add_succ]
  rw [← Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.partialTraj_succ_eq_comp (by omega : b ≤ b + t)]
  rw [Kernel.map_comp]
  rw [Kernel.map_partialTraj_succ_self]
  rw [Kernel.comp_apply]
  rw [markovChainStep]
  rw [map_bind_kernel
    (Kernel.partialTraj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b (b + t) x₀)
    (fun z ↦ z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩)
    (by fun_prop) P]
  apply Measure.bind_congr_right
  filter_upwards with z
  rw [Kernel.comap_apply]

lemma trajectoryStateMarginal_eq_from_current
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b t x₀ =
      trajectoryStateMarginal P 0 t
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  induction t with
  | zero =>
      rw [trajectoryStateMarginal_zero, trajectoryStateMarginal_zero]
  | succ t ih =>
      rw [trajectoryStateMarginal_succ,
        trajectoryStateMarginal_succ, ih]

lemma map_traj_eval_eq_trajectoryStateMarginal
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) b x₀).map
        (fun ω ↦ ω (b + t)) =
      trajectoryStateMarginal P b t x₀ := by
  rw [trajectoryStateMarginal]
  rw [show (fun ω : ℕ → S ↦ ω (b + t)) =
      (fun z : (j : Finset.Iic (b + t)) → S ↦
        z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩) ∘
      Preorder.frestrictLe (π := fun _ : ℕ ↦ S) (b + t) by rfl]
  rw [← Measure.map_map]
  · have hproj :=
      Kernel.traj_map_frestrictLe_apply
        (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
        b (b + t) x₀
    rw [hproj]
  · fun_prop
  · fun_prop

lemma map_traj_eval_eq_map_markovChainMeasure_eval
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) b x₀).map
        (fun ω ↦ ω (b + t)) =
      (markovChainMeasure P
        (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun ω ↦ ω t) := by
  rw [markovChainMeasure_eq_traj_zero]
  calc
    (Kernel.traj (X := fun _ : ℕ ↦ S)
        (markovChainStep P) b x₀).map (fun ω ↦ ω (b + t)) =
        trajectoryStateMarginal P b t x₀ :=
      map_traj_eval_eq_trajectoryStateMarginal P b t x₀
    _ = trajectoryStateMarginal P 0 t
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
      trajectoryStateMarginal_eq_from_current P b t x₀
    _ = (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun ω ↦ ω t) := by
      simpa using
        (map_traj_eval_eq_trajectoryStateMarginal P 0 t
          (fun _ : Finset.Iic 0 ↦
            x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).symm

lemma constNat_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S] (m : ℕ) :
    IsTrajStoppingTime (fun _ : ℕ → S ↦ (m : ℕ∞)) := by
  intro t
  by_cases hmt : m ≤ t
  · convert MeasurableSet.univ
    ext ω
    simp [hmt]
  · convert MeasurableSet.empty
    ext ω
    simp [hmt]

lemma discountedStoppedSum_const_succ
    {S : Type*} (α : ℝ) (f : S → ℝ) (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun _ ↦ ((n + 1 : ℕ) : ℕ∞)) ω =
      discountedStoppedSum α f (fun _ ↦ (n : ℕ∞)) ω +
        α ^ n * f (ω n) := by
  rw [discountedStoppedSum_coe_nat,
    discountedStoppedSum_coe_nat,
    finiteRetirementSegment, finiteRetirementSegment]
  rw [Finset.sum_range_succ]
  simp

lemma integrable_markovChain_eval_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (t : ℕ) :
    Integrable (fun ω : ℕ → S ↦ r (ω t))
      (markovChainMeasure P x) := by
  have hsucc := integrable_discountedStoppedSum P hr hα0.le hint x
    (constNat_isTrajStoppingTime (S := S) (t + 1))
  have hprev := integrable_discountedStoppedSum P hr hα0.le hint x
    (constNat_isTrajStoppingTime (S := S) t)
  have hdiff := hsucc.sub hprev
  have heq :
      (fun ω : ℕ → S ↦
        discountedStoppedSum α r
            (fun _ ↦ ((t + 1 : ℕ) : ℕ∞)) ω -
          discountedStoppedSum α r (fun _ ↦ (t : ℕ∞)) ω) =
        fun ω ↦ α ^ t * r (ω t) := by
    funext ω
    rw [discountedStoppedSum_const_succ]
    ring
  change Integrable (fun ω : ℕ → S ↦
      discountedStoppedSum α r
          (fun _ ↦ ((t + 1 : ℕ) : ℕ∞)) ω -
        discountedStoppedSum α r (fun _ ↦ (t : ℕ∞)) ω)
      (markovChainMeasure P x) at hdiff
  rw [heq] at hdiff
  have hscaled := hdiff.const_mul (α ^ t)⁻¹
  simpa [mul_assoc, pow_ne_zero t hα0.ne'] using hscaled

lemma integrable_traj_eval_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (fun ω : ℕ → S ↦ r (ω (b + t)))
      (Kernel.traj (markovChainStep P) b x₀) := by
  have hmap :
      Integrable r
        ((markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
            (fun ω : ℕ → S ↦ ω t)) := by
    exact (integrable_map_measure hr.aestronglyMeasurable
      (measurable_pi_apply t).aemeasurable).2
        (integrable_markovChain_eval_of_discounted
          P hr hα0 hint
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) t)
  rw [← map_traj_eval_eq_map_markovChainMeasure_eval P b t x₀] at hmap
  exact hmap.comp_measurable (measurable_pi_apply (b + t))

lemma integrable_finiteRetirementPayoff_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (b n : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (finiteRetirementPayoff P r α γ b n)
      (Kernel.traj (markovChainStep P) b x₀) := by
  apply integrable_finiteRetirementPayoff P hr α γ b n
  intro j hj
  exact integrable_traj_eval_of_discounted
    P hr hα0 hint b j x₀

lemma integrable_finiteRetirementPayoff_next_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (b n : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (finiteRetirementPayoff P r α γ (b + 1) n)
      (Kernel.traj (markovChainStep P) b x₀) := by
  apply integrable_finiteRetirementPayoff P hr α γ (b + 1) n
  intro j hj
  simpa [Nat.add_assoc, Nat.add_comm 1 j] using
    (integrable_traj_eval_of_discounted
      P hr hα0 hint b (j + 1) x₀)

theorem integral_discountedStoppedSum_finiteRetirementForcedTime_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (n : ℕ) (x : S) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦
          ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) ω
        ∂markovChainMeasure P x) =
      r x - γ +
        α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x := by
  exact integral_discountedStoppedSum_finiteRetirementForcedTime
    P hr α γ
    (fun b n x₀ ↦
      integrable_finiteRetirementPayoff_of_discounted
        P hr hα0 hint γ b n x₀)
    (fun b n x₀ ↦
      integrable_finiteRetirementPayoff_next_of_discounted
        P hr hα0 hint γ b n x₀)
    n x

lemma finiteRetirementForcedTime_isStoppingTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) (n : ℕ) :
    IsTrajStoppingTime
      (fun ω ↦ ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)) := by
  intro t
  cases t with
  | zero =>
      convert MeasurableSet.empty
      ext ω
      simp
  | succ t =>
      have h :=
        measurableSet_finiteRetirementTime_le P hr α γ 1 n t
      have heq : 1 + t = t + 1 := by omega
      rw [← heq]
      have hset :
          {ω | ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞) ≤
              ((1 + t : ℕ) : ℕ∞)} =
            {ω | finiteRetirementTime P r α γ 1 n ω ≤ t} := by
        ext ω
        norm_cast
        simp
      rw [hset]
      exact h

lemma gittinsRetirementCandidateSet_bddAbove
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) :
    BddAbove (insert 0 {v : ℝ |
      ∃ τ : (ℕ → S) → ℕ∞,
        IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
          ∂markovChainMeasure P x}) := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  let U : ℝ := (gittinsIndex P r α x - γ) * G
  refine ⟨max 0 U, ?_⟩
  intro v hv
  rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
  · exact le_max_left _ _
  · rw [integral_discountedStoppedSum_sub_charge
      P hr hα0.le hα1 hint x hτ]
    let den : ℝ :=
      ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
        ∂markovChainMeasure P x
    let num : ℝ :=
      ∫ ω, discountedStoppedSum α r τ ω
        ∂markovChainMeasure P x
    have hbounds :=
      integral_discountedStoppedSum_one_bounds
        P hα0.le hα1 x hτ hτ1
    have hden : 0 < den := by
      dsimp [den]
      linarith [hbounds.1]
    have hdenG : den ≤ G := by
      exact hbounds.2
    have hratio : num / den ≤ gittinsIndex P r α x :=
      gittins_stopping_ratio_le_index
        P hr hα0 hα1 hint x τ hτ hτ1
    have hnum : num ≤ gittinsIndex P r α x * den := by
      rwa [div_le_iff₀ hden] at hratio
    have hnet :
        num - γ * den ≤
          (gittinsIndex P r α x - γ) * den := by
      nlinarith
    apply hnet.trans
    by_cases hδ : 0 ≤ gittinsIndex P r α x - γ
    · exact (mul_le_mul_of_nonneg_left hdenG hδ).trans
        (le_max_right _ _)
    · have hδ' : gittinsIndex P r α x - γ < 0 := lt_of_not_ge hδ
      have : (gittinsIndex P r α x - γ) * den ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hδ'.le hden.le
      exact this.trans (le_max_left _ _)

theorem gittinsFiniteRetirementValue_le_retirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (n : ℕ) (x : S) :
    gittinsFiniteRetirementValue P r α γ n x ≤
      gittinsRetirementValue P r α γ x := by
  let B : Set ℝ := insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x}
  have hBdd : BddAbove B :=
    gittinsRetirementCandidateSet_bddAbove
      P hr hα0 hα1 hint x γ
  have hzero : (0 : ℝ) ∈ B := Set.mem_insert 0 _
  have hzle : 0 ≤ gittinsRetirementValue P r α γ x := by
    rw [gittinsRetirementValue]
    change 0 ≤ sSup B
    exact le_csSup hBdd hzero
  cases n with
  | zero =>
      simpa [gittinsFiniteRetirementValue] using hzle
  | succ n =>
      let V : ℝ :=
        gittinsFiniteRetirementValue P r α γ (n + 1) x
      let c : ℝ :=
        r x - γ +
          α * ∫ y, gittinsFiniteRetirementValue P r α γ n y ∂P x
      have hV : V = max 0 c := by
        rfl
      by_cases hV0 : V = 0
      · simpa [V, hV0] using hzle
      · have hVnonneg : 0 ≤ V := by
          rw [hV]
          exact le_max_left _ _
        have hVpos : 0 < V := lt_of_le_of_ne hVnonneg (Ne.symm hV0)
        have hcpos : 0 < c := by
          by_contra hc
          have hcle : c ≤ 0 := le_of_not_gt hc
          have : V = 0 := by
            rw [hV, max_eq_left hcle]
          exact hV0 this
        let τ : (ℕ → S) → ℕ∞ :=
          fun ω ↦
            ((1 + finiteRetirementTime P r α γ 1 n ω : ℕ) : ℕ∞)
        have hτ : IsTrajStoppingTime τ :=
          finiteRetirementForcedTime_isStoppingTime P hr α γ n
        have hτ1 : ∀ ω, 1 ≤ τ ω := by
          intro ω
          simp [τ]
        have hvalue :
            (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
                ∂markovChainMeasure P x) = V := by
          rw [integral_discountedStoppedSum_finiteRetirementForcedTime_of_discounted
            P hr hα0 hint γ n x]
          rw [hV, max_eq_right hcpos.le]
        have hmem : V ∈ B := by
          right
          exact ⟨τ, hτ, hτ1, hvalue.symm⟩
        rw [gittinsRetirementValue]
        change V ≤ sSup B
        exact le_csSup hBdd hmem

noncomputable def finiteBellmanWealth
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    (N t : ℕ) (ω : ℕ → S) : ℝ :=
  let u := min t N
  finiteRetirementSegment α (fun x ↦ r x - γ) 0 u ω +
    α ^ u * gittinsFiniteRetirementValue P r α γ (N - u) (ω u)

lemma finiteBellmanWealth_of_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    {N t : ℕ} (ht : t ≤ N) (ω : ℕ → S) :
    finiteBellmanWealth P r α γ N t ω =
      finiteRetirementSegment α (fun x ↦ r x - γ) 0 t ω +
        α ^ t *
          gittinsFiniteRetirementValue P r α γ (N - t) (ω t) := by
  simp [finiteBellmanWealth, min_eq_left ht]

lemma finiteBellmanWealth_of_ge
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ)
    {N t : ℕ} (ht : N ≤ t) (ω : ℕ → S) :
    finiteBellmanWealth P r α γ N t ω =
      finiteRetirementSegment α (fun x ↦ r x - γ) 0 N ω := by
  simp [finiteBellmanWealth, min_eq_right ht,
    gittinsFiniteRetirementValue]

lemma gittinsFiniteRetirementValue_nonneg
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (r : S → ℝ) (α γ : ℝ) :
    ∀ n x, 0 ≤ gittinsFiniteRetirementValue P r α γ n x := by
  intro n x
  cases n with
  | zero => simp [gittinsFiniteRetirementValue]
  | succ n =>
      rw [gittinsFiniteRetirementValue]
      exact le_max_left _ _

lemma finiteBellmanWealth_stronglyAdapted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ) (N : ℕ) :
    StronglyAdapted
      (Filtration.piLE (X := fun _ : ℕ ↦ S))
      (finiteBellmanWealth P r α γ N) := by
  intro t
  rw [Filtration.piLE_eq_comap_frestrictLe]
  change StronglyMeasurable[trajectoryFiltration S t]
    (finiteBellmanWealth P r α γ N t)
  let u := min t N
  have hut : u ≤ t := min_le_left _ _
  apply Measurable.stronglyMeasurable
  rw [show finiteBellmanWealth P r α γ N t =
      fun ω ↦
        ∑ j ∈ Finset.range u,
            α ^ j * (r (ω j) - γ) +
          α ^ u *
            gittinsFiniteRetirementValue P r α γ (N - u) (ω u) by
        funext ω
        simp [finiteBellmanWealth, finiteRetirementSegment, u]]
  apply Measurable.add
  · apply Finset.measurable_sum
    intro j hj
    have hjt : j ≤ t := by
      have hju : j < u := Finset.mem_range.1 hj
      omega
    exact measurable_const.mul
      ((hr.comp (measurable_trajectory_eval_le hjt)).sub measurable_const)
  · exact measurable_const.mul
      ((measurable_gittinsFiniteRetirementValue
        P hr α γ (N - u)).comp
          (measurable_trajectory_eval_le hut))

lemma integral_traj_eval_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : StronglyMeasurable f)
    (t : ℕ) (x₀ : (j : Finset.Iic t) → S) :
    (∫ ω, f (ω (t + 1))
        ∂Kernel.traj (X := fun _ : ℕ ↦ S)
          (markovChainStep P) t x₀) =
      ∫ y, f y ∂P (x₀ ⟨t, Finset.mem_Iic.2 le_rfl⟩) := by
  rw [← MeasureTheory.integral_map_of_stronglyMeasurable
    (by fun_prop : Measurable (fun ω : ℕ → S ↦ ω (t + 1))) hf]
  rw [← Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.map_traj_succ_self]
  rw [markovChainStep, Kernel.comap_apply]

theorem integrable_gittinsFiniteRetirementValue_along_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) :
    ∀ n b t (x₀ : (j : Finset.Iic b) → S),
      Integrable
        (fun ω : ℕ → S ↦
          gittinsFiniteRetirementValue P r α γ n (ω (b + t)))
        (Kernel.traj (markovChainStep P) b x₀) := by
  intro n
  induction n with
  | zero =>
      intro b t x₀
      simp [gittinsFiniteRetirementValue]
  | succ n ih =>
      intro b t x₀
      let s := b + t
      let V : S → ℝ :=
        gittinsFiniteRetirementValue P r α γ n
      let K : S → ℝ := fun y ↦ ∫ z, V z ∂P y
      have hnext :
          Integrable (fun ω : ℕ → S ↦ V (ω (s + 1)))
            (Kernel.traj (markovChainStep P) b x₀) := by
        simpa [V, s, Nat.add_assoc] using ih b (t + 1) x₀
      have hcond :=
        Kernel.condExp_traj
          (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
          (a := b) (b := s) (by omega : b ≤ s)
          (x₀ := x₀) hnext
      let C : (ℕ → S) → ℝ :=
        MeasureTheory.condExp
          (Filtration.piLE (X := fun _ : ℕ ↦ S) s)
          (Kernel.traj (markovChainStep P) b x₀)
          (fun ω ↦ V (ω (s + 1)))
      have hcondInt :
          Integrable C
            (Kernel.traj (markovChainStep P) b x₀) :=
        integrable_condExp
      have heq :
          C =ᵐ[
              Kernel.traj (markovChainStep P) b x₀]
            fun ω ↦ K (ω s) := by
        change C =ᵐ[
            Kernel.traj (markovChainStep P) b x₀]
          (fun x ↦
            ∫ y, V (y (s + 1))
              ∂Kernel.traj (markovChainStep P) s
                (Preorder.frestrictLe s x)) at hcond
        filter_upwards [hcond] with ω hω
        rw [hω]
        exact integral_traj_eval_succ P V
          (measurable_gittinsFiniteRetirementValue
            P hr α γ n).stronglyMeasurable s
          (Preorder.frestrictLe s ω)
      have hK : Integrable (fun ω : ℕ → S ↦ K (ω s))
          (Kernel.traj (markovChainStep P) b x₀) :=
        hcondInt.congr heq
      have hrcoord :
          Integrable (fun ω : ℕ → S ↦ r (ω s))
            (Kernel.traj (markovChainStep P) b x₀) := by
        simpa [s] using
          integrable_traj_eval_of_discounted
            P hr hα0 hint b t x₀
      have htotal :
          Integrable
            (fun ω : ℕ → S ↦
              r (ω s) - γ + α * K (ω s))
            (Kernel.traj (markovChainStep P) b x₀) := by
        exact (hrcoord.sub (integrable_const γ)).add
          (hK.const_mul α)
      rw [show (fun ω : ℕ → S ↦
          gittinsFiniteRetirementValue P r α γ (n + 1) (ω (b + t))) =
          fun ω ↦ max 0 (r (ω s) - γ + α * K (ω s)) by
            funext ω
            simp [gittinsFiniteRetirementValue, s, V, K]]
      simpa [max_comm] using htotal.pos_part

theorem integrable_gittinsFiniteRetirementValue_kernel
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (n : ℕ) (x : S) :
    Integrable (gittinsFiniteRetirementValue P r α γ n) (P x) := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hpath :=
    integrable_gittinsFiniteRetirementValue_along_traj
      P hr hα0 hint γ n 0 1 x₀
  have hmap :
      (Kernel.traj (markovChainStep P) 0 x₀).map
          (fun ω : ℕ → S ↦ ω 1) = P x := by
    rw [← Kernel.map_apply _ (by fun_prop)]
    rw [Kernel.map_traj_succ_self]
    rw [markovChainStep, Kernel.comap_apply]
  have hpush :
      Integrable (gittinsFiniteRetirementValue P r α γ n)
        ((Kernel.traj (markovChainStep P) 0 x₀).map
          (fun ω : ℕ → S ↦ ω 1)) := by
    exact (integrable_map_measure
      (measurable_gittinsFiniteRetirementValue
        P hr α γ n).stronglyMeasurable.aestronglyMeasurable
      (measurable_pi_apply 1).aemeasurable).2 (by simpa using hpath)
  rw [hmap] at hpush
  exact hpush

theorem integrable_finiteBellmanWealth_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (N t : ℕ) (x : S) :
    Integrable (finiteBellmanWealth P r α γ N t)
      (markovChainMeasure P x) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  let u := min t N
  have hseg :
      Integrable
        (fun ω : ℕ → S ↦
          finiteRetirementSegment α (fun z ↦ r z - γ) 0 u ω)
        (markovChainMeasure P x) := by
    apply integrable_finiteRetirementSegment_random
      hr α γ (fun _ ↦ u) u
      (fun j ↦ by
        by_cases hju : j < u
        · convert MeasurableSet.univ <;> ext ω <;> simp [hju]
        · convert MeasurableSet.empty <;> ext ω <;> simp [hju])
      (fun _ ↦ le_rfl)
    intro j hj
    exact integrable_markovChain_eval_of_discounted
      P hr hα0 hint x j
  have hV :
      Integrable
        (fun ω : ℕ → S ↦
          gittinsFiniteRetirementValue P r α γ (N - u) (ω u))
        (markovChainMeasure P x) := by
    rw [markovChainMeasure_eq_traj_zero]
    simpa [u] using
      integrable_gittinsFiniteRetirementValue_along_traj
        P hr hα0 hint γ (N - u) 0 u
          (fun _ : Finset.Iic 0 ↦ x)
  rw [show finiteBellmanWealth P r α γ N t =
      fun ω ↦
        finiteRetirementSegment α (fun z ↦ r z - γ) 0 u ω +
          α ^ u *
            gittinsFiniteRetirementValue P r α γ (N - u) (ω u) by
        funext ω
        simp [finiteBellmanWealth, u]]
  exact hseg.add (hV.const_mul (α ^ u))

lemma measurable_finiteRetirementSegment
    {S : Type*} [MeasurableSpace S]
    {q : S → ℝ} (hq : Measurable q) (α : ℝ) (b m : ℕ) :
    Measurable (finiteRetirementSegment α q b m) := by
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul
    (hq.comp (measurable_pi_apply (b + j)))

lemma finiteRetirementSegment_append
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) :
    finiteRetirementSegment α q b (m + 1) ω =
      finiteRetirementSegment α q b m ω +
        α ^ m * q (ω (b + m)) := by
  rw [finiteRetirementSegment, finiteRetirementSegment]
  rw [Finset.sum_range_succ]

lemma integral_finiteBellmanWealth_succ_le
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α) (γ : ℝ)
    {N t : ℕ} (ht : t < N)
    (x : ℕ → S)
    (hV : Integrable
      (gittinsFiniteRetirementValue P r α γ (N - t - 1))
      (P (x t))) :
    (∫ ω, finiteBellmanWealth P r α γ N (t + 1) ω
        ∂Kernel.traj (markovChainStep P) t
          (Preorder.frestrictLe t x)) ≤
      finiteBellmanWealth P r α γ N t x := by
  let x₀ : (j : Finset.Iic t) → S :=
    Preorder.frestrictLe t x
  let V : S → ℝ :=
    gittinsFiniteRetirementValue P r α γ (N - t - 1)
  have ht1 : t + 1 ≤ N := by omega
  have hmwealth : Measurable
      (finiteBellmanWealth P r α γ N (t + 1)) := by
    rw [show finiteBellmanWealth P r α γ N (t + 1) =
        fun ω ↦
          finiteRetirementSegment α (fun z ↦ r z - γ) 0 (t + 1) ω +
            α ^ (t + 1) * V (ω (t + 1)) by
          funext ω
          rw [finiteBellmanWealth_of_le P r α γ ht1]
          congr 2]
    exact (measurable_finiteRetirementSegment
      (hr.sub measurable_const) α 0 (t + 1)).add
        (measurable_const.mul
          ((measurable_gittinsFiniteRetirementValue
            P hr α γ (N - t - 1)).comp
              (measurable_pi_apply (t + 1))))
  have hfix :=
    Kernel.integral_traj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      x₀ hmwealth.stronglyMeasurable.aestronglyMeasurable
  rw [hfix]
  have hfun :
      (fun ω : ℕ → S ↦
        finiteBellmanWealth P r α γ N (t + 1)
          (Function.updateFinset ω (Finset.Iic t) x₀)) =
        fun ω ↦
          finiteRetirementSegment α (fun z ↦ r z - γ) 0 t x +
            α ^ t *
              (r (x t) - γ + α * V (ω (t + 1))) := by
    funext ω
    rw [finiteBellmanWealth_of_le P r α γ ht1]
    rw [finiteRetirementSegment_append]
    have hseg :
        finiteRetirementSegment α (fun z ↦ r z - γ) 0 t
            (Function.updateFinset ω (Finset.Iic t) x₀) =
          finiteRetirementSegment α (fun z ↦ r z - γ) 0 t x := by
      rw [finiteRetirementSegment, finiteRetirementSegment]
      apply Finset.sum_congr rfl
      intro j hj
      have hjt : j ≤ t := by
        have : j < t := Finset.mem_range.1 hj
        omega
      simp [Function.updateFinset, x₀, hjt]
    rw [hseg]
    have hcurrent :
        Function.updateFinset ω (Finset.Iic t) x₀ (0 + t) = x t := by
      simp [Function.updateFinset, x₀]
    rw [hcurrent]
    have hnext :
        Function.updateFinset ω (Finset.Iic t) x₀ (t + 1) =
          ω (t + 1) := by
      simp [Function.updateFinset]
    rw [hnext]
    dsimp [V]
    have hsub : N - (t + 1) = N - t - 1 := by omega
    rw [hsub, pow_succ]
    ring
  rw [hfun]
  have hVmap :
      Integrable V
        ((Kernel.traj (markovChainStep P) t x₀).map
          (fun ω : ℕ → S ↦ ω (t + 1))) := by
    have hmap :
        (Kernel.traj (markovChainStep P) t x₀).map
            (fun ω : ℕ → S ↦ ω (t + 1)) =
          P (x t) := by
      rw [← Kernel.map_apply _ (by fun_prop)]
      rw [Kernel.map_traj_succ_self]
      rw [markovChainStep, Kernel.comap_apply]
      simp [x₀]
    rw [hmap]
    exact hV
  have hVtraj : Integrable (fun ω : ℕ → S ↦ V (ω (t + 1)))
      (Kernel.traj (markovChainStep P) t x₀) :=
    hVmap.comp_measurable (measurable_pi_apply (t + 1))
  have hinner : Integrable
      (fun ω : ℕ → S ↦
        α ^ t * (r (x t) - γ + α * V (ω (t + 1))))
      (Kernel.traj (markovChainStep P) t x₀) := by
    simpa only [Pi.add_apply] using
      (((integrable_const (r (x t) - γ)).add
        (hVtraj.const_mul α)).const_mul (α ^ t))
  rw [integral_add
    (integrable_const
      (finiteRetirementSegment α (fun z ↦ r z - γ) 0 t x))
    hinner]
  rw [integral_const_mul]
  rw [integral_add
    (integrable_const (r (x t) - γ))
    (hVtraj.const_mul α)]
  rw [integral_const_mul]
  rw [integral_traj_eval_succ P V
    (measurable_gittinsFiniteRetirementValue
      P hr α γ (N - t - 1)).stronglyMeasurable t x₀]
  rw [finiteBellmanWealth_of_le P r α γ ht.le]
  have hbell :
      r (x t) - γ + α * ∫ y, V y ∂P (x t) ≤
        gittinsFiniteRetirementValue P r α γ (N - t) (x t) := by
    have hsub : N - t = (N - t - 1) + 1 := by omega
    rw [hsub, gittinsFiniteRetirementValue]
    exact le_max_right _ _
  have hscaled := mul_le_mul_of_nonneg_left hbell (pow_nonneg hα0 t)
  have hadd := add_le_add_left hscaled
    (finiteRetirementSegment α (fun z ↦ r z - γ) 0 t x)
  simpa [x₀] using hadd

theorem finiteBellmanWealth_supermartingale
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α) (γ : ℝ)
    (N : ℕ) (x : S)
    (hV : ∀ n y,
      Integrable (gittinsFiniteRetirementValue P r α γ n) (P y))
    (hwealth : ∀ t,
      Integrable (finiteBellmanWealth P r α γ N t)
        (markovChainMeasure P x)) :
    Supermartingale
      (finiteBellmanWealth P r α γ N)
      (Filtration.piLE (X := fun _ : ℕ ↦ S))
      (markovChainMeasure P x) := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  rw [markovChainMeasure_eq_traj_zero] at hwealth ⊢
  apply supermartingale_nat
    (finiteBellmanWealth_stronglyAdapted P hr α γ N)
    hwealth
  intro t
  by_cases ht : t < N
  · have hcond :=
      Kernel.condExp_traj
        (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
        (a := 0) (b := t) (Nat.zero_le t)
        (x₀ := x₀) (hwealth (t + 1))
    filter_upwards [hcond] with ω hω
    rw [hω]
    exact integral_finiteBellmanWealth_succ_le
      P hr hα0 γ ht ω (hV (N - t - 1) (ω t))
  · have hNt : N ≤ t := le_of_not_gt ht
    have hfun :
        finiteBellmanWealth P r α γ N (t + 1) =
          finiteBellmanWealth P r α γ N t := by
      funext ω
      rw [finiteBellmanWealth_of_ge P r α γ (by omega)]
      rw [finiteBellmanWealth_of_ge P r α γ hNt]
    rw [hfun]
    have hadp :=
      finiteBellmanWealth_stronglyAdapted P hr α γ N
    rw [condExp_of_stronglyMeasurable
      (Filtration.le (Filtration.piLE (X := fun _ : ℕ ↦ S)) t)
      (hadp t) (hwealth t)]

theorem integral_discountedStoppedSum_nat_le_finiteRetirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (N : ℕ) (x : S)
    (m : (ℕ → S) → ℕ)
    (hm : IsTrajStoppingTime (fun ω ↦ (m ω : ℕ∞)))
    (hmN : ∀ ω, m ω ≤ N)
    (hV : ∀ n y,
      Integrable (gittinsFiniteRetirementValue P r α γ n) (P y))
    (hwealth : ∀ t,
      Integrable (finiteBellmanWealth P r α γ N t)
        (markovChainMeasure P x)) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦ (m ω : ℕ∞)) ω
        ∂markovChainMeasure P x) ≤
      gittinsFiniteRetirementValue P r α γ N x := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
    Filtration.piLE (X := fun _ : ℕ ↦ S)
  let σ : (ℕ → S) → ℕ∞ := fun ω ↦ (m ω : ℕ∞)
  have hσ : IsStoppingTime ℱ σ := by
    intro t
    dsimp [ℱ, σ]
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact hm t
  have hzero : IsStoppingTime ℱ (fun _ : ℕ → S ↦ (0 : ℕ∞)) :=
    isStoppingTime_const ℱ 0
  have h0σ : (fun _ : ℕ → S ↦ (0 : ℕ∞)) ≤ σ := by
    intro ω
    exact bot_le
  have hσN : ∀ ω, σ ω ≤ (N : ℕ∞) := by
    intro ω
    change (m ω : ℕ∞) ≤ (N : ℕ∞)
    exact_mod_cast hmN ω
  have hsuper :=
    finiteBellmanWealth_supermartingale
      P hr hα0.le γ N x hV hwealth
  have hoptional :=
    MeasureTheory.Submartingale.expected_stoppedValue_mono hsuper.neg
      hzero hσ h0σ hσN
  have hwealthStop :
      Integrable
        (stoppedValue (finiteBellmanWealth P r α γ N) σ)
        (markovChainMeasure P x) :=
    by
      have hneg :=
        MeasureTheory.Submartingale.integrable_stoppedValue
          hsuper.neg hσ hσN
      have hnegneg := hneg.neg
      have heq :
          -stoppedValue (-finiteBellmanWealth P r α γ N) σ =
            stoppedValue (finiteBellmanWealth P r α γ N) σ := by
        funext ω
        simp [stoppedValue]
      rw [heq] at hnegneg
      exact hnegneg
  have hsegment :
      Integrable
        (fun ω ↦
          finiteRetirementSegment α (fun z ↦ r z - γ) 0 (m ω) ω)
        (markovChainMeasure P x) := by
    apply integrable_finiteRetirementSegment_random
      hr α γ m N
      (fun j ↦ by
        rw [show {ω : ℕ → S | j < m ω} =
            {ω : ℕ → S | (m ω : ℕ∞) ≤ (j : ℕ∞)}ᶜ by
              ext ω
              simp]
        have hfil :
            trajectoryFiltration S j ≤
              (inferInstance : MeasurableSpace (ℕ → S)) := by
          intro A hA
          rcases hA with ⟨B, hB, rfl⟩
          exact hB.preimage (by fun_prop)
        exact (hfil _ (hm j)).compl)
      hmN
    intro j hj
    exact integrable_markovChain_eval_of_discounted
      P hr hα0 hint x j
  have hpoint :
      ∀ ω,
        finiteRetirementSegment α (fun z ↦ r z - γ) 0 (m ω) ω ≤
          stoppedValue (finiteBellmanWealth P r α γ N) σ ω := by
    intro ω
    simp only [stoppedValue, σ]
    rw [show ((m ω : ℕ∞).untopA : ℕ) = m ω by simp]
    rw [finiteBellmanWealth_of_le P r α γ (hmN ω)]
    have hnonneg :
        0 ≤ α ^ m ω *
          gittinsFiniteRetirementValue P r α γ (N - m ω) (ω (m ω)) :=
      mul_nonneg (pow_nonneg hα0.le _) <|
        gittinsFiniteRetirementValue_nonneg P r α γ _ _
    linarith
  have hintle :
      (∫ ω,
          finiteRetirementSegment α (fun z ↦ r z - γ) 0 (m ω) ω
          ∂markovChainMeasure P x) ≤
        ∫ ω, stoppedValue (finiteBellmanWealth P r α γ N) σ ω
          ∂markovChainMeasure P x :=
    integral_mono hsegment hwealthStop hpoint
  rw [show (fun ω ↦ discountedStoppedSum α (fun y ↦ r y - γ)
      (fun ω ↦ (m ω : ℕ∞)) ω) =
      fun ω ↦
        finiteRetirementSegment α (fun z ↦ r z - γ) 0 (m ω) ω by
          funext ω
          exact discountedStoppedSum_coe_nat
            α (fun y ↦ r y - γ) m ω]
  calc
    _ ≤ ∫ ω, stoppedValue (finiteBellmanWealth P r α γ N) σ ω
          ∂markovChainMeasure P x := hintle
    _ ≤ ∫ ω, finiteBellmanWealth P r α γ N 0 ω
          ∂markovChainMeasure P x := by
      change (∫ ω, -finiteBellmanWealth P r α γ N 0 ω
          ∂markovChainMeasure P x) ≤
        ∫ ω, -stoppedValue (finiteBellmanWealth P r α γ N) σ ω
          ∂markovChainMeasure P x at hoptional
      rw [integral_neg, integral_neg] at hoptional
      exact neg_le_neg_iff.mp hoptional
    _ = gittinsFiniteRetirementValue P r α γ N x := by
      rw [markovChainMeasure_eq_traj_zero]
      let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
      have hfix :=
        Kernel.integral_traj
          (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
          x₀
          ((measurable_gittinsFiniteRetirementValue
            P hr α γ N).comp
              (measurable_pi_apply 0)).stronglyMeasurable.aestronglyMeasurable
      rw [show (fun ω : ℕ → S ↦
          finiteBellmanWealth P r α γ N 0 ω) =
          fun ω ↦ gittinsFiniteRetirementValue P r α γ N (ω 0) by
            funext ω
            simp [finiteBellmanWealth, finiteRetirementSegment]]
      have hfix' :
          (∫ ω, gittinsFiniteRetirementValue P r α γ N (ω 0)
              ∂Kernel.traj (X := fun _ : ℕ ↦ S)
                (markovChainStep P) 0 x₀) =
            ∫ ω, gittinsFiniteRetirementValue P r α γ N
                ((Function.updateFinset ω (Finset.Iic 0) x₀) 0)
              ∂Kernel.traj (X := fun _ : ℕ ↦ S)
                (markovChainStep P) 0 x₀ := by
        simpa only [Function.comp_apply] using hfix
      rw [hfix']
      simp [Function.updateFinset, x₀]

theorem integral_discountedStoppedSum_nat_le_finiteRetirementValue_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (N : ℕ) (x : S)
    (m : (ℕ → S) → ℕ)
    (hm : IsTrajStoppingTime (fun ω ↦ (m ω : ℕ∞)))
    (hmN : ∀ ω, m ω ≤ N) :
    (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
        (fun ω ↦ (m ω : ℕ∞)) ω
        ∂markovChainMeasure P x) ≤
      gittinsFiniteRetirementValue P r α γ N x := by
  exact integral_discountedStoppedSum_nat_le_finiteRetirementValue
    P hr hα0 hα1 hint γ N x m hm hmN
    (fun n y ↦ integrable_gittinsFiniteRetirementValue_kernel
      P hr hα0 hint γ n y)
    (fun t ↦ integrable_finiteBellmanWealth_of_discounted
      P hr hα0 hint γ N t x)

noncomputable def truncatedStoppedSum
    {S : Type*} (α : ℝ) (f : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (N : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ t ∈ Finset.range N,
    if (t : ℕ∞) < τ ω then α ^ t * f (ω t) else 0

private lemma measurableSet_lt_trajStoppingTime
    {S : Type*} [MeasurableSpace S] {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) (t : ℕ) :
    MeasurableSet {ω | (t : ℕ∞) < τ ω} := by
  rw [show {ω | (t : ℕ∞) < τ ω} =
      {ω | τ ω ≤ (t : ℕ∞)}ᶜ by ext ω; simp]
  have hfil :
      trajectoryFiltration S t ≤
        (inferInstance : MeasurableSpace (ℕ → S)) := by
    intro A hA
    rcases hA with ⟨B, hB, rfl⟩
    exact hB.preimage (by fun_prop)
  exact (hfil _ (hτ t)).compl

lemma measurable_truncatedStoppedSum
    {S : Type*} [MeasurableSpace S]
    {α : ℝ} {f : S → ℝ} (hf : Measurable f)
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (N : ℕ) :
    Measurable (truncatedStoppedSum α f τ N) := by
  apply Finset.measurable_sum
  intro t ht
  exact Measurable.ite (measurableSet_lt_trajStoppingTime hτ t)
    (measurable_const.mul (hf.comp (measurable_pi_apply t)))
    measurable_const

private lemma measurable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|) := by
  apply Measurable.tsum
  intro t
  exact measurable_const.mul
    (by
      have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop)

private lemma measurable_discountedAbsSeriesENNReal
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.ennreal_tsum
  intro t
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul
      (by
        have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
          hr.comp (measurable_pi_apply t)
        fun_prop))

private lemma ae_summable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_discountedAbsSeriesENNReal hr)
      (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

private lemma integrable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|)
      (markovChainMeasure P x) := by
  refine ⟨(measurable_discountedAbsSeries hr).aestronglyMeasurable, ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂markovChainMeasure P x,
        0 ≤ ∑' t : ℕ, α ^ t * |r (ω t)| :=
    Filter.Eventually.of_forall fun ω ↦ tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal (∑' t : ℕ, α ^ t * |r (ω t)|)
        ∂markovChainMeasure P x) =
        ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P x := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_summable_discountedAbsSeries P hr hα0 hint x]
        with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hint x

noncomputable def discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (x : S) : ℝ :=
  ∫ ω, ∑' t : ℕ, α ^ t * |r (ω t)|
    ∂markovChainMeasure P x

private lemma discountedStoppedSum_le_discountedAbsSeries
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α)
    (r : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hsum : Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|)) :
    discountedStoppedSum α r τ ω ≤
      ∑' t : ℕ, α ^ t * |r (ω t)| := by
  let a : ℕ → ℝ :=
    fun t ↦ if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
  have ha : Summable a := by
    apply Summable.of_norm_bounded hsum
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [a, ht, abs_of_nonneg hα0]
    · simp [a, ht, mul_nonneg
        (pow_nonneg hα0 t) (abs_nonneg _)]
  have hanorm : Summable (fun t ↦ ‖a t‖) := ha.norm
  have hnorm :
      ‖∑' t, a t‖ ≤ ∑' t, ‖a t‖ :=
    norm_tsum_le_tsum_norm hanorm
  have hsumle :
      (∑' t, ‖a t‖) ≤
        ∑' t : ℕ, α ^ t * |r (ω t)| := by
    exact hanorm.tsum_le_tsum
      (fun t ↦ by
        by_cases ht : (t : ℕ∞) < τ ω
        · simp [a, ht, abs_of_nonneg hα0]
        · simp [a, ht, mul_nonneg
            (pow_nonneg hα0 t) (abs_nonneg _)])
      hsum
  change (∑' t, a t) ≤
    ∑' t : ℕ, α ^ t * |r (ω t)|
  exact (le_abs_self _).trans (hnorm.trans hsumle)

theorem gittinsRetirementValue_le_absReward_add_charge
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    gittinsRetirementValue P r α γ x ≤
      discountedAbsoluteRewardValue P r α x +
        |γ| * ∑' t : ℕ, α ^ t := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  let A : ℝ := discountedAbsoluteRewardValue P r α x
  let U : ℝ := A + |γ| * G
  let B : Set ℝ := insert 0 {v : ℝ |
    ∃ τ : (ℕ → S) → ℕ∞,
      IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
      v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x}
  have hRint :
      Integrable (fun ω : ℕ → S ↦
        ∑' t : ℕ, α ^ t * |r (ω t)|)
        (markovChainMeasure P x) :=
    integrable_discountedAbsSeries P hr hα0.le hint x
  have hA0 : 0 ≤ A := by
    dsimp [A, discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  have hG0 : 0 ≤ G :=
    tsum_nonneg fun t ↦ pow_nonneg hα0.le t
  have hBU : ∀ v ∈ B, v ≤ U := by
    intro v hv
    rcases hv with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
    · dsimp [U]
      exact add_nonneg hA0 (mul_nonneg (abs_nonneg γ) hG0)
    · rw [integral_discountedStoppedSum_sub_charge
        P hr hα0.le hα1 hint x hτ]
      let den : ℝ :=
        ∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x
      let num : ℝ :=
        ∫ ω, discountedStoppedSum α r τ ω
          ∂markovChainMeasure P x
      have hnumint :
          Integrable (discountedStoppedSum α r τ)
            (markovChainMeasure P x) :=
        integrable_discountedStoppedSum P hr hα0.le hint x hτ
      have hnumA : num ≤ A := by
        dsimp [num, A, discountedAbsoluteRewardValue]
        apply integral_mono_ae hnumint hRint
        filter_upwards
          [ae_summable_discountedAbsSeries
            P hr hα0.le hint x] with ω hsum
        exact discountedStoppedSum_le_discountedAbsSeries
          hα0.le r τ ω hsum
      have hbounds :=
        integral_discountedStoppedSum_one_bounds
          P hα0.le hα1 x hτ hτ1
      have hden0 : 0 ≤ den := by
        dsimp [den]
        linarith [hbounds.1]
      have hdenG : den ≤ G := by
        simpa [den, G] using hbounds.2
      have hneg :
          -γ * den ≤ |γ| * G := by
        calc
          -γ * den ≤ |γ| * den :=
            mul_le_mul_of_nonneg_right (neg_le_abs γ) hden0
          _ ≤ |γ| * G :=
            mul_le_mul_of_nonneg_left hdenG (abs_nonneg γ)
      dsimp [num, den, U]
      linarith
  have hBdd : BddAbove B := ⟨U, hBU⟩
  rw [gittinsRetirementValue]
  change sSup B ≤ A + |γ| * G
  exact csSup_le ⟨0, Set.mem_insert 0 _⟩ hBU

noncomputable def discountedAbsoluteRewardFuture
    {S : Type*} (r : S → ℝ) (α : ℝ)
    (b : ℕ) (ω : ℕ → S) : ℝ :=
  ∑' t : ℕ, α ^ t * |r (ω (b + t))|

private lemma measurable_discountedAbsoluteRewardFuture
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ) (b : ℕ) :
    Measurable (discountedAbsoluteRewardFuture r α b) := by
  apply Measurable.tsum
  intro t
  fun_prop

private lemma measurable_discountedAbsoluteRewardFutureENNReal
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ) (b : ℕ) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)) := by
  apply Measurable.ennreal_tsum
  intro t
  fun_prop

lemma lintegral_traj_eval_eq_markovChain_eval
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ENNReal) (hf : Measurable f)
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫⁻ (ω : ℕ → S), f (ω (b + t))
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫⁻ (ω : ℕ → S), f (ω t)
        ∂markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  have hleft :
      (∫⁻ y, f y ∂
        ((Kernel.traj (markovChainStep P) b x₀).map
          (fun ω : ℕ → S ↦ ω (b + t)))) =
        ∫⁻ (ω : ℕ → S), f (ω (b + t))
          ∂Kernel.traj (markovChainStep P) b x₀ :=
    MeasureTheory.lintegral_map
      hf (measurable_pi_apply (b + t))
  have hright :
      (∫⁻ y, f y ∂
        ((markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
            (fun ω : ℕ → S ↦ ω t))) =
        ∫⁻ (ω : ℕ → S), f (ω t)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
    MeasureTheory.lintegral_map hf (measurable_pi_apply t)
  rw [map_traj_eval_eq_map_markovChainMeasure_eval P b t x₀] at hleft
  exact hleft.symm.trans hright

lemma lintegral_discountedAbsoluteRewardFutureENNReal_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (α : ℝ) (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω t)|)
        ∂markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  calc
    (∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
        ∂Kernel.traj (markovChainStep P) b x₀) =
        ∑' t : ℕ, ∫⁻ (ω : ℕ → S),
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
          ∂Kernel.traj (markovChainStep P) b x₀ :=
      MeasureTheory.lintegral_tsum
        (fun t ↦ (by fun_prop :
          Measurable (fun ω : ℕ → S ↦
            ENNReal.ofReal
              (α ^ t * |r (ω (b + t))|))).aemeasurable)
    _ = ∑' t : ℕ, ∫⁻ (ω : ℕ → S),
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
      apply tsum_congr
      intro t
      exact lintegral_traj_eval_eq_markovChain_eval
        P (fun y ↦ ENNReal.ofReal (α ^ t * |r y|))
        (by fun_prop) b t x₀
    _ = ∫⁻ (ω : ℕ → S), ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
      (MeasureTheory.lintegral_tsum
        (fun t ↦ (by fun_prop :
          Measurable (fun ω : ℕ → S ↦
            ENNReal.ofReal
              (α ^ t * |r (ω t)|))).aemeasurable)).symm

lemma integrable_discountedAbsoluteRewardFuture_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (discountedAbsoluteRewardFuture r α b)
      (Kernel.traj (markovChainStep P) b x₀) := by
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b x₀
  have hlin :
      (∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ) < ⊤ := by
    rw [lintegral_discountedAbsoluteRewardFutureENNReal_traj
      P hr α b x₀]
    exact hint (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)
  have hfinite :
      ∀ᵐ ω ∂μ,
        (∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|)) < ⊤ :=
    ae_lt_top
      (measurable_discountedAbsoluteRewardFutureENNReal
        hr α b) (ne_of_lt hlin)
  have hsummable :
      ∀ᵐ ω ∂μ,
        Summable (fun t : ℕ ↦
          α ^ t * |r (ω (b + t))|) := by
    filter_upwards [hfinite] with ω hω
    have hs := ENNReal.summable_toReal (ne_of_lt hω)
    simpa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs
  refine ⟨
    (measurable_discountedAbsoluteRewardFuture
      hr α b).aestronglyMeasurable,
    ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂μ,
        0 ≤ discountedAbsoluteRewardFuture r α b ω :=
    Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal
        (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
        ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hsummable] with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hlin

theorem integral_discountedAbsoluteRewardFuture_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ ω, discountedAbsoluteRewardFuture r α b ω
        ∂Kernel.traj (markovChainStep P) b x₀) =
      discountedAbsoluteRewardValue P r α
        (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b x₀
  let y := x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩
  have hleft :=
    integrable_discountedAbsoluteRewardFuture_traj
      P hr hα0 hint b x₀
  have hright :=
    integrable_discountedAbsSeries P hr hα0 hint y
  have hleft0 :
      0 ≤ ∫ ω, discountedAbsoluteRewardFuture r α b ω ∂μ :=
    integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  have hright0 :
      0 ≤ discountedAbsoluteRewardValue P r α y := by
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  apply (ENNReal.ofReal_eq_ofReal_iff hleft0 hright0).mp
  dsimp [discountedAbsoluteRewardValue]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hleft (Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hright (Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))]
  change
    (∫⁻ ω, ENNReal.ofReal
      (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
    ∫⁻ ω, ENNReal.ofReal
      (∑' t : ℕ, α ^ t * |r (ω t)|)
      ∂markovChainMeasure P y
  have hlin :
      (∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ) < ⊤ := by
    rw [lintegral_discountedAbsoluteRewardFutureENNReal_traj
      P hr α b x₀]
    exact hint y
  have hleftsum :
      ∀ᵐ ω ∂μ,
        Summable (fun t : ℕ ↦
          α ^ t * |r (ω (b + t))|) := by
    have hfinite :
        ∀ᵐ ω ∂μ,
          (∑' t : ℕ,
            ENNReal.ofReal
              (α ^ t * |r (ω (b + t))|)) < ⊤ :=
      ae_lt_top
        (measurable_discountedAbsoluteRewardFutureENNReal
          hr α b) (ne_of_lt hlin)
    filter_upwards [hfinite] with ω hω
    have hs := ENNReal.summable_toReal (ne_of_lt hω)
    simpa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs
  calc
    (∫⁻ ω, ENNReal.ofReal
        (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
        ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hleftsum] with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ = ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P y :=
      lintegral_discountedAbsoluteRewardFutureENNReal_traj
        P hr α b x₀
    _ = ∫⁻ ω, ENNReal.ofReal
          (∑' t : ℕ, α ^ t * |r (ω t)|)
          ∂markovChainMeasure P y := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_summable_discountedAbsSeries
          P hr hα0 hint y] with ω hω
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω).symm

lemma integrable_discountedAbsoluteRewardFuture_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    Integrable (discountedAbsoluteRewardFuture r α N)
      (markovChainMeasure P x) := by
  let R : (ℕ → S) → ℝ :=
    fun ω ↦ ∑' t : ℕ, α ^ t * |r (ω t)|
  let Q : (ℕ → S) → ℝ :=
    fun ω ↦ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)|
  have hR : Integrable R (markovChainMeasure P x) :=
    integrable_discountedAbsSeries P hr hα0.le hint x
  have hQ : Integrable Q (markovChainMeasure P x) := by
    apply MeasureTheory.integrable_finset_sum
    intro t ht
    exact (integrable_markovChain_eval_of_discounted
      P hr hα0 hint x t).norm.const_mul (α ^ t)
  have hdiff := hR.sub hQ
  have heq :
      (fun ω ↦ R ω - Q ω) =ᵐ[markovChainMeasure P x]
        fun ω ↦ α ^ N *
          discountedAbsoluteRewardFuture r α N ω := by
    filter_upwards
      [ae_summable_discountedAbsSeries
        P hr hα0.le hint x] with ω hs
    have hsplit := hs.sum_add_tsum_nat_add N
    dsimp [R, Q, discountedAbsoluteRewardFuture]
    rw [← hsplit]
    simp only [add_sub_cancel_left]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [pow_add]
    rw [Nat.add_comm t N]
    ring
  have hscaledInt :
      Integrable
        (fun ω ↦ α ^ N *
          discountedAbsoluteRewardFuture r α N ω)
        (markovChainMeasure P x) :=
    hdiff.congr heq
  have hscaled := hscaledInt.const_mul (α ^ N)⁻¹
  simpa [mul_assoc, pow_ne_zero N hα0.ne'] using hscaled

set_option maxHeartbeats 800000 in
theorem integrable_discountedAbsoluteRewardValue_along_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    Integrable
      (fun ω : ℕ → S ↦
        discountedAbsoluteRewardValue P r α (ω N))
      (markovChainMeasure P x) ∧
    (∫ ω, discountedAbsoluteRewardValue P r α (ω N)
        ∂markovChainMeasure P x) =
      ∫ ω, discountedAbsoluteRewardFuture r α N ω
        ∂markovChainMeasure P x := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) 0 x₀
  let F : (ℕ → S) → ℝ :=
    discountedAbsoluteRewardFuture r α N
  have hFmarkov :
      Integrable F (markovChainMeasure P x) :=
    integrable_discountedAbsoluteRewardFuture_markov
      P hr hα0 hint x N
  have hmeasure : markovChainMeasure P x = μ := by
    rw [markovChainMeasure_eq_traj_zero]
  have hF : Integrable F μ := by
    rwa [← hmeasure]
  have hcond :=
    Kernel.condExp_traj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      (a := 0) (b := N) (Nat.zero_le N)
      (x₀ := x₀) hF
  let C : (ℕ → S) → ℝ :=
    MeasureTheory.condExp
      (Filtration.piLE (X := fun _ : ℕ ↦ S) N)
      μ F
  have hCint : Integrable C μ := integrable_condExp
  have heq :
      C =ᵐ[μ] fun ω ↦
        discountedAbsoluteRewardValue P r α (ω N) := by
    filter_upwards [hcond] with ω hω
    change
      MeasureTheory.condExp
        (Filtration.piLE (X := fun _ : ℕ ↦ S) N)
        μ F ω =
        discountedAbsoluteRewardValue P r α (ω N)
    rw [hω]
    simpa [F] using
      (integral_discountedAbsoluteRewardFuture_traj
        P hr hα0.le hint N (Preorder.frestrictLe N ω))
  have hAintμ :
      Integrable
        (fun ω : ℕ → S ↦
          discountedAbsoluteRewardValue P r α (ω N)) μ :=
    hCint.congr heq
  have hintEqμ :
      (∫ ω, discountedAbsoluteRewardValue P r α (ω N) ∂μ) =
        ∫ ω, F ω ∂μ := by
    rw [← integral_congr_ae heq]
    exact integral_condExp
      (Filtration.le
        (Filtration.piLE (X := fun _ : ℕ ↦ S)) N)
  constructor
  · rw [hmeasure]
    exact hAintμ
  · rw [hmeasure]
    simpa [F] using hintEqμ

theorem tendsto_integral_truncatedStoppedSum
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) :
    Tendsto
      (fun N ↦ ∫ ω, truncatedStoppedSum α r τ N ω
        ∂markovChainMeasure P x)
      atTop
      (𝓝 (∫ ω, discountedStoppedSum α r τ ω
        ∂markovChainMeasure P x)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun ω : ℕ → S ↦ ∑' t : ℕ, α ^ t * |r (ω t)|)
  · intro N
    exact (measurable_truncatedStoppedSum hr hτ N).aestronglyMeasurable
  · exact integrable_discountedAbsSeries P hr hα0 hint x
  · intro N
    filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
      with ω hsum
    calc
      ‖truncatedStoppedSum α r τ N ω‖ ≤
          ∑ t ∈ Finset.range N,
            ‖if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)| := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases hstop : (t : ℕ∞) < τ ω
        · simp [hstop, abs_of_nonneg hα0]
        · simp [hstop, mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)]
      _ ≤ ∑' t : ℕ, α ^ t * |r (ω t)| :=
        hsum.sum_le_tsum (Finset.range N)
          (fun t ht ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))
  · filter_upwards [ae_summable_discountedAbsSeries P hr hα0 hint x]
      with ω hsum
    let a : ℕ → ℝ := fun t ↦
      if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
    have ha : Summable a := by
      apply Summable.of_norm_bounded hsum
      intro t
      by_cases hstop : (t : ℕ∞) < τ ω
      · simp [a, hstop, abs_of_nonneg hα0]
      · simp [a, hstop,
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)]
    change Tendsto (fun N ↦ ∑ t ∈ Finset.range N, a t)
      atTop (𝓝 (∑' t, a t))
    simpa only [Finset.sum_filter] using ha.hasSum.tendsto_sum_nat

noncomputable def truncatedStoppingNat
    {S : Type*} (τ : (ℕ → S) → ℕ∞) (N : ℕ)
    (ω : ℕ → S) : ℕ :=
  (min (τ ω) (N : ℕ∞)).toNat

lemma coe_truncatedStoppingNat
    {S : Type*} (τ : (ℕ → S) → ℕ∞) (N : ℕ)
    (ω : ℕ → S) :
    (truncatedStoppingNat τ N ω : ℕ∞) =
      min (τ ω) (N : ℕ∞) := by
  apply ENat.coe_toNat
  exact ne_top_of_le_ne_top (by simp) (min_le_right _ _)

lemma truncatedStoppingNat_le
    {S : Type*} (τ : (ℕ → S) → ℕ∞) (N : ℕ)
    (ω : ℕ → S) :
    truncatedStoppingNat τ N ω ≤ N := by
  apply ENat.coe_le_coe.mp
  rw [coe_truncatedStoppingNat]
  exact min_le_right _ _

lemma truncatedStoppingNat_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S]
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (N : ℕ) :
    IsTrajStoppingTime
      (fun ω ↦ (truncatedStoppingNat τ N ω : ℕ∞)) := by
  intro t
  have hset :
      {ω | (truncatedStoppingNat τ N ω : ℕ∞) ≤ (t : ℕ∞)} =
        {ω | min (τ ω) (N : ℕ∞) ≤ (t : ℕ∞)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [coe_truncatedStoppingNat]
  rw [hset]
  by_cases hNt : N ≤ t
  · convert MeasurableSet.univ
    ext ω
    simp [hNt]
  · have htN : t < N := lt_of_not_ge hNt
    have heq :
        {ω | min (τ ω) (N : ℕ∞) ≤ (t : ℕ∞)} =
          {ω | τ ω ≤ (t : ℕ∞)} := by
      ext ω
      simp only [min_le_iff]
      norm_cast
      simp [not_le.mpr htN]
    rw [heq]
    exact hτ t

lemma discountedStoppedSum_truncatedStoppingNat
    {S : Type*} (α : ℝ) (f : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (N : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f
        (fun z ↦ (truncatedStoppingNat τ N z : ℕ∞)) ω =
      truncatedStoppedSum α f τ N ω := by
  rw [discountedStoppedSum]
  rw [tsum_eq_sum (s := Finset.range N)]
  · rw [truncatedStoppedSum]
    apply Finset.sum_congr rfl
    intro t ht
    have htN : t < N := Finset.mem_range.1 ht
    rw [coe_truncatedStoppingNat]
    simp [htN]
  · intro t ht
    have hNt : N ≤ t := by
      simpa only [Finset.mem_range, not_lt] using ht
    rw [coe_truncatedStoppingNat]
    simp [not_lt_of_ge hNt]

theorem tendsto_integral_truncatedStoppedSum_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (x : S) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) :
    Tendsto
      (fun N ↦ ∫ ω, truncatedStoppedSum α (fun _ : S ↦ 1) τ N ω
        ∂markovChainMeasure P x)
      atTop
      (𝓝 (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
        ∂markovChainMeasure P x)) := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  have hgeom : Summable (fun t : ℕ ↦ α ^ t) :=
    summable_geometric_of_norm_lt_one (K := ℝ) (by
      rw [Real.norm_eq_abs, abs_of_nonneg hα0]
      exact hα1)
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  apply tendsto_integral_of_dominated_convergence (fun _ : ℕ → S ↦ G)
  · intro N
    exact (measurable_truncatedStoppedSum measurable_const hτ N).aestronglyMeasurable
  · exact integrable_const G
  · intro N
    filter_upwards with ω
    calc
      ‖truncatedStoppedSum α (fun _ : S ↦ 1) τ N ω‖ ≤
          ∑ t ∈ Finset.range N, α ^ t := by
        rw [truncatedStoppedSum]
        calc
          ‖∑ t ∈ Finset.range N,
              if (t : ℕ∞) < τ ω then α ^ t * 1 else 0‖ ≤
              ∑ t ∈ Finset.range N,
                ‖if (t : ℕ∞) < τ ω then α ^ t * 1 else 0‖ :=
            norm_sum_le _ _
          _ ≤ ∑ t ∈ Finset.range N, α ^ t := by
            apply Finset.sum_le_sum
            intro t ht
            by_cases hs : (t : ℕ∞) < τ ω
            · simp [hs, abs_of_nonneg hα0]
            · simp [hs, pow_nonneg hα0 t]
      _ ≤ G :=
        hgeom.sum_le_tsum (Finset.range N)
          (fun t ht ↦ pow_nonneg hα0 t)
  · filter_upwards with ω
    let a : ℕ → ℝ := fun t ↦
      if (t : ℕ∞) < τ ω then α ^ t * 1 else 0
    have ha : Summable a := by
      apply Summable.of_norm_bounded hgeom
      intro t
      by_cases hs : (t : ℕ∞) < τ ω
      · simp [a, hs, abs_of_nonneg hα0]
      · simp [a, hs, pow_nonneg hα0 t]
    change Tendsto (fun N ↦ ∑ t ∈ Finset.range N, a t)
      atTop (𝓝 (∑' t, a t))
    simpa only [Finset.sum_filter] using ha.hasSum.tendsto_sum_nat

lemma truncatedStoppedSum_sub_charge
    {S : Type*} (α γ : ℝ) (r : S → ℝ)
    (τ : (ℕ → S) → ℕ∞) (N : ℕ) (ω : ℕ → S) :
    truncatedStoppedSum α (fun y ↦ r y - γ) τ N ω =
      truncatedStoppedSum α r τ N ω -
        γ * truncatedStoppedSum α (fun _ : S ↦ 1) τ N ω := by
  rw [truncatedStoppedSum, truncatedStoppedSum, truncatedStoppedSum]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : (t : ℕ∞) < τ ω
  · simp [hs]
    ring
  · simp [hs]

theorem tendsto_integral_truncatedStoppedSum_sub_charge
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) {τ : (ℕ → S) → ℕ∞}
    (hτ : IsTrajStoppingTime τ) :
    Tendsto
      (fun N ↦ ∫ ω,
        truncatedStoppedSum α (fun y ↦ r y - γ) τ N ω
          ∂markovChainMeasure P x)
      atTop
      (𝓝 (∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
        ∂markovChainMeasure P x)) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  have hrLim :=
    tendsto_integral_truncatedStoppedSum P hr hα0.le hint x hτ
  have h1Lim :=
    tendsto_integral_truncatedStoppedSum_one P hα0.le hα1 x hτ
  have hcomb := hrLim.sub (h1Lim.const_mul γ)
  convert hcomb using 1
  · funext N
    rw [show (fun ω ↦
        truncatedStoppedSum α (fun y ↦ r y - γ) τ N ω) =
        fun ω ↦ truncatedStoppedSum α r τ N ω -
          γ * truncatedStoppedSum α (fun _ : S ↦ 1) τ N ω by
          funext ω
          exact truncatedStoppedSum_sub_charge α γ r τ N ω]
    have htr :
        IsTrajStoppingTime
          (fun ω ↦ (truncatedStoppingNat τ N ω : ℕ∞)) :=
      truncatedStoppingNat_isTrajStoppingTime hτ N
    have hrInt :
        Integrable (truncatedStoppedSum α r τ N)
          (markovChainMeasure P x) := by
      have hi :=
        integrable_discountedStoppedSum P hr hα0.le hint x htr
      apply hi.congr
      filter_upwards with ω
      exact discountedStoppedSum_truncatedStoppingNat
        α r τ N ω
    have h1Int :
        Integrable (truncatedStoppedSum α (fun _ : S ↦ 1) τ N)
          (markovChainMeasure P x) := by
      have hi :=
        integrable_discountedStoppedSum_one P hα0.le hα1 x htr
      apply hi.congr
      filter_upwards with ω
      exact discountedStoppedSum_truncatedStoppingNat
        α (fun _ : S ↦ 1) τ N ω
    rw [integral_sub]
    · rw [integral_const_mul]
    · exact hrInt
    · exact h1Int.const_mul γ
  · rw [integral_discountedStoppedSum_sub_charge
      P hr hα0.le hα1 hint x hτ]

theorem tendsto_gittinsFiniteRetirementValue_retirementValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    Tendsto
      (fun n ↦ gittinsFiniteRetirementValue P r α γ n x)
      atTop
      (𝓝 (gittinsRetirementValue P r α γ x)) := by
  let V : ℕ → ℝ :=
    fun n ↦ gittinsFiniteRetirementValue P r α γ n x
  have hVint : ∀ n y,
      Integrable (gittinsFiniteRetirementValue P r α γ n) (P y) :=
    fun n y ↦ integrable_gittinsFiniteRetirementValue_kernel
      P hr hα0 hint γ n y
  have hmono : Monotone V :=
    monotone_nat_of_le_succ fun n ↦
      gittinsFiniteRetirementValue_mono_of_integrable
        P r α γ hα0.le hVint n x
  have hub : ∀ n, V n ≤ gittinsRetirementValue P r α γ x :=
    fun n ↦ gittinsFiniteRetirementValue_le_retirementValue
      P hr hα0 hα1 hint γ n x
  have hbdd : BddAbove (Set.range V) :=
    ⟨gittinsRetirementValue P r α γ x, by
      intro z hz
      rcases hz with ⟨n, rfl⟩
      exact hub n⟩
  have hsup :
      (⨆ n, V n) = gittinsRetirementValue P r α γ x := by
    apply le_antisymm
    · exact ciSup_le hub
    · let B : Set ℝ := insert 0 {v : ℝ |
        ∃ τ : (ℕ → S) → ℕ∞,
          IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
          v = ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ) τ ω
            ∂markovChainMeasure P x}
      rw [gittinsRetirementValue]
      change sSup B ≤ ⨆ n, V n
      apply csSup_le
      · exact ⟨0, Set.mem_insert 0 _⟩
      · intro z hz
        rcases hz with (rfl | ⟨τ, hτ, hτ1, rfl⟩)
        · have hzero : V 0 = 0 := by
            simp [V, gittinsFiniteRetirementValue]
          rw [← hzero]
          exact le_ciSup hbdd 0
        · have hlim :=
            tendsto_integral_truncatedStoppedSum_sub_charge
              P hr hα0 hα1 hint x γ hτ
          apply le_of_tendsto hlim
          filter_upwards with N
          let m : (ℕ → S) → ℕ :=
            truncatedStoppingNat τ N
          have hm :
              IsTrajStoppingTime (fun ω ↦ (m ω : ℕ∞)) :=
            truncatedStoppingNat_isTrajStoppingTime hτ N
          have hmN : ∀ ω, m ω ≤ N :=
            truncatedStoppingNat_le τ N
          calc
            (∫ ω,
                truncatedStoppedSum α (fun y ↦ r y - γ) τ N ω
                ∂markovChainMeasure P x) =
                ∫ ω, discountedStoppedSum α (fun y ↦ r y - γ)
                    (fun z ↦ (m z : ℕ∞)) ω
                  ∂markovChainMeasure P x := by
              apply integral_congr_ae
              filter_upwards with ω
              exact (discountedStoppedSum_truncatedStoppingNat
                α (fun y ↦ r y - γ) τ N ω).symm
            _ ≤ V N := integral_discountedStoppedSum_nat_le_finiteRetirementValue_of_discounted
              P hr hα0 hα1 hint γ N x m hm hmN
            _ ≤ ⨆ n, V n := le_ciSup hbdd N
  rw [← hsup]
  exact tendsto_atTop_ciSup hmono hbdd

theorem measurable_gittinsRetirementValue_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) :
    Measurable (gittinsRetirementValue P r α γ) := by
  exact measurable_gittinsRetirementValue_of_finite_tendsto
    P hr α γ
    (tendsto_gittinsFiniteRetirementValue_retirementValue
      P hr hα0 hα1 hint γ)

theorem integrable_gittinsRetirementValue_kernel_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    Integrable (gittinsRetirementValue P r α γ) (P x) := by
  let V : ℕ → S → ℝ :=
    fun n ↦ gittinsFiniteRetirementValue P r α γ n
  let W : S → ℝ :=
    gittinsRetirementValue P r α γ
  let C : ℝ :=
    (W x + |r x - γ|) / α
  have hVint : ∀ n y, Integrable (V n) (P y) :=
    fun n y ↦ integrable_gittinsFiniteRetirementValue_kernel
      P hr hα0 hint γ n y
  have hVnonneg : ∀ n y, 0 ≤ V n y :=
    fun n y ↦ gittinsFiniteRetirementValue_nonneg P r α γ n y
  have hVleW : ∀ n y, V n y ≤ W y :=
    fun n y ↦ gittinsFiniteRetirementValue_le_retirementValue
      P hr hα0 hα1 hint γ n y
  have hIntBound : ∀ n, ∫ y, V n y ∂P x ≤ C := by
    intro n
    apply (le_div_iff₀ hα0).2
    rw [mul_comm]
    have hbell :
        r x - γ + α * ∫ y, V n y ∂P x ≤ V (n + 1) x := by
      exact le_max_right 0 _
    have habs : -(r x - γ) ≤ |r x - γ| := neg_le_abs _
    linarith [hVleW (n + 1) x]
  have hLinf :
      liminf (fun n ↦ ∫⁻ y, ‖V n y‖ₑ ∂P x) atTop ≠ ⊤ := by
    have hbound :
        liminf (fun n ↦ ∫⁻ y, ‖V n y‖ₑ ∂P x) atTop ≤
          ENNReal.ofReal C := by
      apply Filter.liminf_le_of_frequently_le'
      exact Filter.Frequently.of_forall fun n ↦ by
        rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
          (hVint n x)]
        apply ENNReal.ofReal_le_ofReal
        calc
          (∫ y, ‖V n y‖ ∂P x) =
              ∫ y, V n y ∂P x := by
            apply integral_congr_ae
            filter_upwards with y
            exact abs_of_nonneg (hVnonneg n y)
          _ ≤ C := hIntBound n
    exact (lt_of_le_of_lt hbound ENNReal.ofReal_lt_top).ne_top
  refine ⟨
    (measurable_gittinsRetirementValue_of_discounted
      P hr hα0 hα1 hint γ).stronglyMeasurable.aestronglyMeasurable,
    ?_⟩
  have hlim :
      ∀ y, Tendsto (fun n ↦ V n y) atTop (𝓝 (W y)) :=
    fun y ↦ tendsto_gittinsFiniteRetirementValue_retirementValue
      P hr hα0 hα1 hint γ y
  calc
    (∫⁻ y, ‖W y‖ₑ ∂P x) =
        ∫⁻ y, liminf (fun n ↦ ‖V n y‖ₑ) atTop ∂P x := by
      apply lintegral_congr
      intro y
      exact (hlim y).enorm.liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ y, ‖V n y‖ₑ ∂P x) atTop :=
      MeasureTheory.lintegral_liminf_le'
        (fun n ↦
          (measurable_gittinsFiniteRetirementValue
            P hr α γ n).enorm.aemeasurable)
    _ < ⊤ := hLinf.lt_top

theorem gittinsRetirementValue_bellman_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    gittinsRetirementValue P r α γ x =
      max 0 (r x - γ +
        α * ∫ y, gittinsRetirementValue P r α γ y ∂P x) := by
  exact gittinsRetirementValue_bellman_of_finite_tendsto
    P hα0.le
    (fun n y ↦ integrable_gittinsFiniteRetirementValue_kernel
      P hr hα0 hint γ n y)
    (integrable_gittinsRetirementValue_kernel_of_discounted
      P hr hα0 hα1 hint γ)
    (tendsto_gittinsFiniteRetirementValue_retirementValue
      P hr hα0 hα1 hint γ)
    x

lemma gittinsRetirementValue_nonneg
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    0 ≤ gittinsRetirementValue P r α γ x := by
  simpa [gittinsFiniteRetirementValue] using
    (gittinsFiniteRetirementValue_le_retirementValue
      P hr hα0 hα1 hint γ 0 x)

theorem integrable_gittinsRetirementValue_along_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) (N : ℕ) :
    Integrable
      (fun ω : ℕ → S ↦
        gittinsRetirementValue P r α γ (ω N))
      (markovChainMeasure P x) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  let G : ℝ := ∑' t : ℕ, α ^ t
  have hA :=
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint x N).1
  have hbound :
      Integrable
        (fun ω : ℕ → S ↦
          discountedAbsoluteRewardValue P r α (ω N) +
            |γ| * G)
        (markovChainMeasure P x) :=
    hA.add (integrable_const (|γ| * G))
  apply hbound.mono'
    ((measurable_gittinsRetirementValue_of_discounted
      P hr hα0 hα1 hint γ).comp
        (measurable_pi_apply N)).stronglyMeasurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω ↦ by
    change |gittinsRetirementValue P r α γ (ω N)| ≤
      discountedAbsoluteRewardValue P r α (ω N) + |γ| * G
    rw [abs_of_nonneg
      (gittinsRetirementValue_nonneg
        P hr hα0 hα1 hint γ (ω N))]
    exact gittinsRetirementValue_le_absReward_add_charge
      P hr hα0 hα1 hint γ (ω N)

theorem gittinsRetirementValue_fair_continuation
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) :
    r x - gittinsIndex P r α x +
        α * ∫ y,
          gittinsRetirementValue P r α
            (gittinsIndex P r α x) y ∂P x = 0 := by
  let g : ℝ := gittinsIndex P r α x
  let δ : ℕ → ℝ := fun n ↦ g - 1 / ((n : ℝ) + 1)
  let W : ℕ → S → ℝ :=
    fun n ↦ gittinsRetirementValue P r α (δ n)
  let Wg : S → ℝ :=
    gittinsRetirementValue P r α g
  let C : ℕ → ℝ :=
    fun n ↦ r x - δ n + α * ∫ y, W n y ∂P x
  let Cg : ℝ :=
    r x - g + α * ∫ y, Wg y ∂P x
  let G : ℝ := ∑' t : ℕ, α ^ t
  have hG0 : 0 ≤ G :=
    tsum_nonneg fun t ↦ pow_nonneg hα0.le t
  have hδg : Tendsto δ atTop (𝓝 g) := by
    have hz :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1))
          atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [δ] using tendsto_const_nhds.sub hz
  have hδlt : ∀ n, δ n < g := by
    intro n
    dsimp [δ]
    have hp : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hWlim : ∀ y, Tendsto (fun n ↦ W n y) atTop (𝓝 (Wg y)) := by
    intro y
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
    · exact Filter.Eventually.of_forall fun n ↦ by
        simpa [Real.norm_eq_abs, W, Wg] using
          gittinsRetirementValue_lipschitz_charge
            P hr hα0 hα1 hint y (δ n) g
    · have habs :
      Tendsto (fun n ↦ |δ n - g|) atTop (𝓝 0) := by
        simpa using
          (hδg.sub (tendsto_const_nhds (x := g))).abs
      simpa [G] using habs.mul_const G
  have hWint : ∀ n, Integrable (W n) (P x) :=
    fun n ↦ integrable_gittinsRetirementValue_kernel_of_discounted
      P hr hα0 hα1 hint (δ n) x
  have hWgint : Integrable Wg (P x) :=
    integrable_gittinsRetirementValue_kernel_of_discounted
      P hr hα0 hα1 hint g x
  have hWnonneg : ∀ n y, 0 ≤ W n y :=
    fun n y ↦ gittinsRetirementValue_nonneg
      P hr hα0 hα1 hint (δ n) y
  have hWgnonneg : ∀ y, 0 ≤ Wg y :=
    fun y ↦ gittinsRetirementValue_nonneg
      P hr hα0 hα1 hint g y
  have hWIntegral :
      Tendsto (fun n ↦ ∫ y, W n y ∂P x)
        atTop (𝓝 (∫ y, Wg y ∂P x)) := by
    let bound : S → ℝ := fun y ↦ Wg y + G
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      bound
    · exact Filter.Eventually.of_forall fun n ↦
        (measurable_gittinsRetirementValue_of_discounted
          P hr hα0 hα1 hint (δ n)).stronglyMeasurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun n ↦
        Filter.Eventually.of_forall fun y ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (hWnonneg n y)]
          have hlip :=
            gittinsRetirementValue_lipschitz_charge
              P hr hα0 hα1 hint y (δ n) g
          have hfrac :
              |δ n - g| ≤ 1 := by
            rw [show |δ n - g| =
                (1 : ℝ) / ((n : ℝ) + 1) by
              have hn0 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
              simp [δ, abs_of_nonneg hn0]]
            apply (div_le_one (by positivity)).2
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          have hprod :
              |δ n - g| * G ≤ G :=
            (mul_le_mul_of_nonneg_right hfrac hG0).trans_eq
              (one_mul G)
          change |W n y - Wg y| ≤ |δ n - g| * G at hlip
          dsimp [W, Wg, bound]
          linarith [le_abs_self (W n y - Wg y)]
    · exact hWgint.add (integrable_const G)
    · exact Filter.Eventually.of_forall hWlim
  have hClim : Tendsto C atTop (𝓝 Cg) := by
    exact (tendsto_const_nhds.sub hδg).add
      (tendsto_const_nhds.mul hWIntegral)
  have hCpos : ∀ n, 0 < C n := by
    intro n
    have hpos :
        0 < gittinsRetirementValue P r α (δ n) x :=
      gittinsRetirementValue_pos_of_lt_index
        P hr hα0 hα1 hint x (δ n) (hδlt n)
    have hbell :=
      gittinsRetirementValue_bellman_of_discounted
        P hr hα0 hα1 hint (δ n) x
    dsimp [W, C]
    rw [hbell] at hpos
    exact (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
  have hCg_nonneg : 0 ≤ Cg :=
    ge_of_tendsto' hClim (fun n ↦ (hCpos n).le)
  have hzero :
      gittinsRetirementValue P r α g x = 0 :=
    (gittinsRetirementValue_eq_zero_iff_index_le
      P hr hα0 hα1 hint x g).2 le_rfl
  have hbellg :=
    gittinsRetirementValue_bellman_of_discounted
      P hr hα0 hα1 hint g x
  have hCg_nonpos : Cg ≤ 0 := by
    dsimp [Wg, Cg]
    rw [hzero] at hbellg
    exact (max_eq_left_iff.mp hbellg.symm)
  change Cg = 0
  exact le_antisymm hCg_nonpos hCg_nonneg

lemma top_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S] :
    IsTrajStoppingTime (fun _ : ℕ → S ↦ (⊤ : ℕ∞)) := by
  intro n
  convert MeasurableSet.empty
  ext ω
  simp

theorem tendsto_discounted_absoluteRewardFuture_integral_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) :
    Tendsto
      (fun N ↦ α ^ N *
        ∫ ω, discountedAbsoluteRewardFuture r α N ω
          ∂markovChainMeasure P x)
      atTop (𝓝 0) := by
  let R : (ℕ → S) → ℝ :=
    fun ω ↦ ∑' t : ℕ, α ^ t * |r (ω t)|
  let Q : ℕ → (ℕ → S) → ℝ :=
    fun N ω ↦ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)|
  have habsMeas : Measurable (fun y ↦ |r y|) := by
    fun_prop
  have hintAbs :
      DiscountedRewardIntegrable P (fun y ↦ |r y|) α := by
    intro y
    simpa only [abs_abs] using hint y
  have hprefix :=
    tendsto_integral_truncatedStoppedSum
      P habsMeas hα0.le hintAbs x
      (top_isTrajStoppingTime (S := S))
  have hprefix' :
      Tendsto
        (fun N ↦ ∫ ω, Q N ω ∂markovChainMeasure P x)
        atTop
        (𝓝 (∫ ω, R ω ∂markovChainMeasure P x)) := by
    simpa [Q, R, truncatedStoppedSum,
      discountedStoppedSum] using hprefix
  have heq : ∀ N,
      α ^ N *
          ∫ ω, discountedAbsoluteRewardFuture r α N ω
            ∂markovChainMeasure P x =
        (∫ ω, R ω ∂markovChainMeasure P x) -
          ∫ ω, Q N ω ∂markovChainMeasure P x := by
    intro N
    have hRint :
        Integrable R (markovChainMeasure P x) :=
      integrable_discountedAbsSeries P hr hα0.le hint x
    have hQint :
        Integrable (Q N) (markovChainMeasure P x) := by
      apply MeasureTheory.integrable_finset_sum
      intro t ht
      exact (integrable_markovChain_eval_of_discounted
        P hr hα0 hint x t).norm.const_mul (α ^ t)
    have hFint :=
      integrable_discountedAbsoluteRewardFuture_markov
        P hr hα0 hint x N
    have hpoint :
        (fun ω ↦ R ω - Q N ω) =ᵐ[markovChainMeasure P x]
          fun ω ↦ α ^ N *
            discountedAbsoluteRewardFuture r α N ω := by
      filter_upwards
        [ae_summable_discountedAbsSeries
          P hr hα0.le hint x] with ω hs
      have hsplit := hs.sum_add_tsum_nat_add N
      dsimp [R, Q, discountedAbsoluteRewardFuture]
      rw [← hsplit]
      simp only [add_sub_cancel_left]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro t
      rw [pow_add, Nat.add_comm t N]
      ring
    rw [← integral_const_mul]
    rw [← integral_sub hRint hQint]
    exact (integral_congr_ae hpoint).symm
  rw [show (fun N ↦ α ^ N *
      ∫ ω, discountedAbsoluteRewardFuture r α N ω
        ∂markovChainMeasure P x) =
      fun N ↦ (∫ ω, R ω ∂markovChainMeasure P x) -
        ∫ ω, Q N ω ∂markovChainMeasure P x by
          funext N
          exact heq N]
  simpa using
    (tendsto_const_nhds
      (x := ∫ ω, R ω ∂markovChainMeasure P x)).sub hprefix'

theorem tendsto_discounted_gittinsRetirementValue_integral_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    Tendsto
      (fun N ↦ α ^ N *
        ∫ ω, gittinsRetirementValue P r α γ (ω N)
          ∂markovChainMeasure P x)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  let G : ℝ := ∑' t : ℕ, α ^ t
  let W : ℕ → (ℕ → S) → ℝ :=
    fun N ω ↦ gittinsRetirementValue P r α γ (ω N)
  let A : ℕ → (ℕ → S) → ℝ :=
    fun N ω ↦ discountedAbsoluteRewardValue P r α (ω N)
  let F : ℕ → (ℕ → S) → ℝ :=
    fun N ↦ discountedAbsoluteRewardFuture r α N
  have hFtail :
      Tendsto
        (fun N ↦ α ^ N *
          ∫ ω, F N ω ∂markovChainMeasure P x)
        atTop (𝓝 0) :=
    tendsto_discounted_absoluteRewardFuture_integral_zero
      P hr hα0 hint x
  have hgeom :
      Tendsto (fun N ↦ α ^ N * (|γ| * G))
        atTop (𝓝 0) :=
    by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          hα0.le hα1).mul_const (|γ| * G)
  apply squeeze_zero'
    (g := fun N ↦
      α ^ N * ∫ ω, F N ω ∂markovChainMeasure P x +
        α ^ N * (|γ| * G))
  · exact Filter.Eventually.of_forall fun N ↦
      mul_nonneg (pow_nonneg hα0.le N)
        (integral_nonneg fun ω ↦
          gittinsRetirementValue_nonneg
            P hr hα0 hα1 hint γ (ω N))
  · exact Filter.Eventually.of_forall fun N ↦ by
      have hWint :=
        integrable_gittinsRetirementValue_along_markov
          P hr hα0 hα1 hint γ x N
      have hAdata :=
        integrable_discountedAbsoluteRewardValue_along_markov
          P hr hα0 hint x N
      have hboundInt :
          Integrable
            (fun ω ↦ A N ω + |γ| * G)
            (markovChainMeasure P x) :=
        hAdata.1.add (integrable_const (|γ| * G))
      have hWA :
          (∫ ω, W N ω ∂markovChainMeasure P x) ≤
            ∫ ω, A N ω + |γ| * G
              ∂markovChainMeasure P x := by
        apply integral_mono hWint hboundInt
        intro ω
        exact gittinsRetirementValue_le_absReward_add_charge
          P hr hα0 hα1 hint γ (ω N)
      have hprob :
          (∫ _ : ℕ → S, |γ| * G ∂markovChainMeasure P x) =
            |γ| * G := by simp
      rw [integral_add hAdata.1 (integrable_const (|γ| * G)),
        hprob, hAdata.2] at hWA
      dsimp [W, A, F] at hWA ⊢
      nlinarith [pow_nonneg hα0.le N]
  · simpa [add_zero] using hFtail.add hgeom

theorem measurable_gittinsIndex_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) :
    Measurable (gittinsIndex P r α) := by
  apply measurable_of_Iic
  intro γ
  have hset :
      (gittinsIndex P r α) ⁻¹' Set.Iic γ =
        (gittinsRetirementValue P r α γ) ⁻¹' {0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_singleton_iff]
    exact (gittinsRetirementValue_eq_zero_iff_index_le
      P hr hα0 hα1 hint x γ).symm
  rw [hset]
  exact (measurable_gittinsRetirementValue_of_discounted
    P hr hα0 hα1 hint γ) (measurableSet_singleton 0)

noncomputable def gittinsRetirementThresholdTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ) :
    (ℕ → S) → ℕ∞ :=
  hittingAfter
    (fun t (ω : ℕ → S) ↦
      gittinsRetirementValue P r α γ (ω t))
    {0} 1

lemma gittinsRetirementThresholdTime_isStoppingTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) :
    IsTrajStoppingTime
      (gittinsRetirementThresholdTime P r α γ) := by
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
    Filtration.piLE (X := fun _ : ℕ ↦ S)
  let u : ℕ → (ℕ → S) → ℝ :=
    fun t ω ↦ gittinsRetirementValue P r α γ (ω t)
  have hu : Adapted ℱ u := by
    intro t
    rw [Filtration.piLE_eq_comap_frestrictLe]
    change Measurable[trajectoryFiltration S t]
      ((gittinsRetirementValue P r α γ) ∘
        (fun ω : ℕ → S ↦ ω t))
    exact (measurable_gittinsRetirementValue_of_discounted
      P hr hα0 hα1 hint γ).comp
        (by
          change Measurable[trajectoryFiltration S t]
            (fun ω : ℕ → S ↦ ω t)
          rw [trajectoryFiltration]
          change Measurable[MeasurableSpace.comap
            (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1) inferInstance]
              ((fun z : (i : Finset.Iic t) → S ↦
                z ⟨t, Finset.mem_Iic.2 le_rfl⟩) ∘
              (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1))
          exact (measurable_pi_apply _).comp (comap_measurable _))
  have hstop :
      IsStoppingTime ℱ
        (gittinsRetirementThresholdTime P r α γ) := by
    exact hu.isStoppingTime_hittingAfter (measurableSet_singleton 0)
  intro t
  have ht := hstop t
  have hfil : ℱ t = trajectoryFiltration S t := by
    dsimp [ℱ, trajectoryFiltration]
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rfl
  rw [← hfil]
  exact ht

lemma one_le_gittinsRetirementThresholdTime
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ) (ω : ℕ → S) :
    1 ≤ gittinsRetirementThresholdTime P r α γ ω := by
  exact le_hittingAfter ω

lemma gittinsRetirementValue_pos_before_threshold
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) {t : ℕ} {ω : ℕ → S}
    (h1t : 1 ≤ t)
    (ht : (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω) :
    0 < gittinsRetirementValue P r α γ (ω t) := by
  have hnot :
      gittinsRetirementValue P r α γ (ω t) ∉ ({0} : Set ℝ) :=
    by
      simpa [gittinsRetirementThresholdTime] using
        (notMem_of_lt_hittingAfter
          (u := fun s (η : ℕ → S) ↦
            gittinsRetirementValue P r α γ (η s))
          (s := ({0} : Set ℝ)) (n := 1) ht h1t)
  exact lt_of_le_of_ne
    (gittinsRetirementValue_nonneg
      P hr hα0 hα1 hint γ (ω t))
    (Ne.symm (by simpa using hnot))

lemma gittinsRetirementValue_eq_zero_at_threshold
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ)
    {n : ℕ} {ω : ℕ → S}
    (hτ :
      gittinsRetirementThresholdTime P r α γ ω = (n : ℕ∞)) :
    gittinsRetirementValue P r α γ (ω n) = 0 := by
  have hne :
      hittingAfter
        (fun t (η : ℕ → S) ↦
          gittinsRetirementValue P r α γ (η t))
        ({0} : Set ℝ) 1 ω ≠ ⊤ := by
    change hittingAfter
      (fun t (η : ℕ → S) ↦
        gittinsRetirementValue P r α γ (η t))
      ({0} : Set ℝ) 1 ω = (n : ℕ∞) at hτ
    intro htop
    rw [hτ] at htop
    exact (ENat.coe_ne_top n) htop
  have hmem :=
    hittingAfter_mem_set_of_ne_top
      (u := fun t (η : ℕ → S) ↦
        gittinsRetirementValue P r α γ (η t))
      (s := ({0} : Set ℝ)) (n := 1) hne
  have huntop :
      (hittingAfter
        (fun t (η : ℕ → S) ↦
          gittinsRetirementValue P r α γ (η t))
        ({0} : Set ℝ) 1 ω).untopA = n := by
    rw [show hittingAfter
        (fun t (η : ℕ → S) ↦
          gittinsRetirementValue P r α γ (η t))
        ({0} : Set ℝ) 1 ω = (n : ℕ∞) by
      simpa [gittinsRetirementThresholdTime] using hτ]
    simp
  rw [huntop] at hmem
  simpa using hmem

lemma measurableSet_before_trajStoppingTime
    {S : Type*} [MeasurableSpace S]
    {τ : (ℕ → S) → ℕ∞} (hτ : IsTrajStoppingTime τ)
    (t : ℕ) :
    MeasurableSet[trajectoryFiltration S t]
      {ω | (t : ℕ∞) < τ ω} := by
  rw [show {ω | (t : ℕ∞) < τ ω} =
      {ω | τ ω ≤ (t : ℕ∞)}ᶜ by
        ext ω
        simp]
  exact (hτ t).compl

theorem setIntegral_markovChain_eval_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : Measurable f)
    (x : S) (t : ℕ)
    (hft1 : Integrable (fun ω : ℕ → S ↦ f (ω (t + 1)))
      (markovChainMeasure P x))
    (E : Set (ℕ → S))
    (hE : MeasurableSet[trajectoryFiltration S t] E) :
    (∫ ω in E, f (ω (t + 1)) ∂markovChainMeasure P x) =
      ∫ ω in E, (∫ y, f y ∂P (ω t))
        ∂markovChainMeasure P x := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) 0 x₀
  have hmeasure : markovChainMeasure P x = μ := by
    rw [markovChainMeasure_eq_traj_zero]
  have hft1μ :
      Integrable (fun ω : ℕ → S ↦ f (ω (t + 1))) μ := by
    rwa [← hmeasure]
  have hcond :=
    Kernel.condExp_traj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      (a := 0) (b := t) (Nat.zero_le t)
      (x₀ := x₀) hft1μ
  have heq :
      MeasureTheory.condExp
          (Filtration.piLE (X := fun _ : ℕ ↦ S) t)
          μ (fun ω : ℕ → S ↦ f (ω (t + 1))) =ᵐ[μ]
        fun ω ↦ ∫ y, f y ∂P (ω t) := by
    filter_upwards [hcond] with ω hω
    rw [hω]
    exact integral_traj_eval_succ
      P f hf.stronglyMeasurable t
        (Preorder.frestrictLe t ω)
  have hfil :
      Filtration.piLE (X := fun _ : ℕ ↦ S) t =
        trajectoryFiltration S t := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rfl
  have hEpi :
      MeasurableSet[
        Filtration.piLE (X := fun _ : ℕ ↦ S) t] E := by
    rwa [hfil]
  rw [hmeasure]
  rw [← MeasureTheory.setIntegral_condExp
    (Filtration.le
      (Filtration.piLE (X := fun _ : ℕ ↦ S)) t)
    hft1μ hEpi]
  have hEglobal : MeasurableSet E :=
    (Filtration.le
      (Filtration.piLE (X := fun _ : ℕ ↦ S)) t) E hEpi
  exact setIntegral_congr_ae hEglobal
    (heq.mono fun ω hω _ => hω)

lemma threshold_survival_succ_eq
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ)
    (t : ℕ) (ω : ℕ → S) :
    (if ((t + 1 : ℕ) : ℕ∞) <
        gittinsRetirementThresholdTime P r α γ ω then
      gittinsRetirementValue P r α γ (ω (t + 1))
    else 0) =
      if (t : ℕ∞) <
          gittinsRetirementThresholdTime P r α γ ω then
        gittinsRetirementValue P r α γ (ω (t + 1))
      else 0 := by
  let τ := gittinsRetirementThresholdTime P r α γ ω
  rw [show ((t + 1 : ℕ) : ℕ∞) = (t : ℕ∞) + 1 by norm_num]
  by_cases hnext : (t : ℕ∞) + 1 < τ
  · have ht : (t : ℕ∞) < τ := by
      have hstep : (t : ℕ∞) < (t : ℕ∞) + 1 :=
        (ENat.add_one_le_iff (ENat.coe_ne_top t)).1 le_rfl
      exact lt_trans hstep hnext
    dsimp [τ] at hnext ht ⊢
    simp [hnext, ht]
  · by_cases ht : (t : ℕ∞) < τ
    · have hlower : ((t + 1 : ℕ) : ℕ∞) ≤ τ := by
        rw [show ((t + 1 : ℕ) : ℕ∞) = (t : ℕ∞) + 1 by norm_num]
        exact (ENat.add_one_le_iff (ENat.coe_ne_top t)).2 ht
      have hupper : τ ≤ ((t + 1 : ℕ) : ℕ∞) :=
        le_of_not_gt hnext
      have hτ : τ = ((t + 1 : ℕ) : ℕ∞) :=
        le_antisymm hupper hlower
      have hzero :
          gittinsRetirementValue P r α γ (ω (t + 1)) = 0 :=
        gittinsRetirementValue_eq_zero_at_threshold
          P r α γ hτ
      dsimp [τ] at hnext ht ⊢
      simp [hnext, ht, hzero]
    · dsimp [τ] at hnext ht ⊢
      simp [hnext, ht]

noncomputable def retirementSurvivalTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ)
    (t : ℕ) (ω : ℕ → S) : ℝ :=
  if (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω then
    α ^ t * gittinsRetirementValue P r α γ (ω t)
  else 0

noncomputable def retirementNetTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ)
    (t : ℕ) (ω : ℕ → S) : ℝ :=
  if (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω then
    α ^ t * (r (ω t) - γ)
  else 0

noncomputable def retirementContinuationTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ)
    (t : ℕ) (ω : ℕ → S) : ℝ :=
  if (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω then
    α ^ (t + 1) *
      ∫ y, gittinsRetirementValue P r α γ y ∂P (ω t)
  else 0

lemma retirementSurvivalTerm_eq_net_add_continuation
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) {t : ℕ} (h1t : 1 ≤ t)
    (ω : ℕ → S) :
    retirementSurvivalTerm P r α γ t ω =
      retirementNetTerm P r α γ t ω +
        retirementContinuationTerm P r α γ t ω := by
  by_cases ht :
      (t : ℕ∞) <
        gittinsRetirementThresholdTime P r α γ ω
  · have hpos :
        0 < gittinsRetirementValue P r α γ (ω t) :=
      gittinsRetirementValue_pos_before_threshold
        P hr hα0 hα1 hint γ h1t ht
    have hbell :=
      gittinsRetirementValue_bellman_of_discounted
        P hr hα0 hα1 hint γ (ω t)
    rw [hbell] at hpos
    have hcontpos :
        0 < r (ω t) - γ +
          α * ∫ y,
            gittinsRetirementValue P r α γ y ∂P (ω t) :=
      (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
    simp [retirementSurvivalTerm, retirementNetTerm,
      retirementContinuationTerm, ht,
      hbell, max_eq_right hcontpos.le, pow_succ]
    ring
  · simp [retirementSurvivalTerm, retirementNetTerm,
      retirementContinuationTerm, ht]

lemma measurableSet_before_retirementThreshold
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (t : ℕ) :
    MeasurableSet
      {ω | (t : ℕ∞) <
        gittinsRetirementThresholdTime P r α γ ω} := by
  have hlocal :=
    measurableSet_before_trajStoppingTime
      (gittinsRetirementThresholdTime_isStoppingTime
        P hr hα0 hα1 hint γ) t
  have hfil :
      Filtration.piLE (X := fun _ : ℕ ↦ S) t =
        trajectoryFiltration S t := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    rfl
  have hglobal :
      MeasurableSet[
        Filtration.piLE (X := fun _ : ℕ ↦ S) t]
        {ω | (t : ℕ∞) <
          gittinsRetirementThresholdTime P r α γ ω} := by
    rwa [hfil]
  exact
    (Filtration.le
      (Filtration.piLE (X := fun _ : ℕ ↦ S)) t) _ hglobal

lemma integrable_retirementSurvivalTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) (t : ℕ) :
    Integrable
      (retirementSurvivalTerm P r α γ t)
      (markovChainMeasure P x) := by
  let E : Set (ℕ → S) :=
    {ω | (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω}
  have hE : MeasurableSet E :=
    measurableSet_before_retirementThreshold
      P hr hα0 hα1 hint γ t
  have hW :
      Integrable
        (fun ω : ℕ → S ↦
          α ^ t * gittinsRetirementValue P r α γ (ω t))
        (markovChainMeasure P x) :=
    (integrable_gittinsRetirementValue_along_markov
      P hr hα0 hα1 hint γ x t).const_mul (α ^ t)
  rw [show retirementSurvivalTerm P r α γ t =
      E.indicator
        (fun ω : ℕ → S ↦
          α ^ t * gittinsRetirementValue P r α γ (ω t)) by
        funext ω
        simp [retirementSurvivalTerm, E, Set.indicator]]
  exact hW.indicator hE

lemma integrable_retirementNetTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) (t : ℕ) :
    Integrable
      (retirementNetTerm P r α γ t)
      (markovChainMeasure P x) := by
  letI : IsProbabilityMeasure (markovChainMeasure P x) := by
    rw [← markovChainKernel_apply]
    infer_instance
  let E : Set (ℕ → S) :=
    {ω | (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω}
  have hE : MeasurableSet E :=
    measurableSet_before_retirementThreshold
      P hr hα0 hα1 hint γ t
  have hq :
      Integrable
        (fun ω : ℕ → S ↦ α ^ t * (r (ω t) - γ))
        (markovChainMeasure P x) :=
    ((integrable_markovChain_eval_of_discounted
      P hr hα0 hint x t).sub (integrable_const γ)).const_mul (α ^ t)
  rw [show retirementNetTerm P r α γ t =
      E.indicator
        (fun ω : ℕ → S ↦ α ^ t * (r (ω t) - γ)) by
        funext ω
        simp [retirementNetTerm, E, Set.indicator]]
  exact hq.indicator hE

lemma integral_retirementContinuationTerm_eq_survival_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) (t : ℕ) :
    (∫ ω, retirementContinuationTerm P r α γ t ω
        ∂markovChainMeasure P x) =
      ∫ ω, retirementSurvivalTerm P r α γ (t + 1) ω
        ∂markovChainMeasure P x := by
  let E : Set (ℕ → S) :=
    {ω | (t : ℕ∞) <
      gittinsRetirementThresholdTime P r α γ ω}
  let W : S → ℝ :=
    gittinsRetirementValue P r α γ
  have hEfil :
      MeasurableSet[trajectoryFiltration S t] E :=
    measurableSet_before_trajStoppingTime
      (gittinsRetirementThresholdTime_isStoppingTime
        P hr hα0 hα1 hint γ) t
  have hE : MeasurableSet E :=
    measurableSet_before_retirementThreshold
      P hr hα0 hα1 hint γ t
  have hWmeas : Measurable W :=
    measurable_gittinsRetirementValue_of_discounted
      P hr hα0 hα1 hint γ
  have hWnext :
      Integrable (fun ω : ℕ → S ↦ W (ω (t + 1)))
        (markovChainMeasure P x) :=
    integrable_gittinsRetirementValue_along_markov
      P hr hα0 hα1 hint γ x (t + 1)
  have hmarkov :
      (∫ ω in E, W (ω (t + 1))
          ∂markovChainMeasure P x) =
        ∫ ω in E, (∫ y, W y ∂P (ω t))
          ∂markovChainMeasure P x :=
    setIntegral_markovChain_eval_succ
      P W hWmeas x t hWnext E hEfil
  calc
    (∫ ω, retirementContinuationTerm P r α γ t ω
        ∂markovChainMeasure P x) =
        α ^ (t + 1) *
          ∫ ω in E, (∫ y, W y ∂P (ω t))
            ∂markovChainMeasure P x := by
      rw [show retirementContinuationTerm P r α γ t =
          E.indicator
            (fun ω : ℕ → S ↦
              α ^ (t + 1) * ∫ y, W y ∂P (ω t)) by
            funext ω
            simp [retirementContinuationTerm, E, W, Set.indicator]]
      rw [integral_indicator hE, integral_const_mul]
    _ = α ^ (t + 1) *
          ∫ ω in E, W (ω (t + 1))
            ∂markovChainMeasure P x := by
      rw [hmarkov]
    _ = ∫ ω, E.indicator
          (fun ω : ℕ → S ↦ α ^ (t + 1) * W (ω (t + 1))) ω
            ∂markovChainMeasure P x := by
      rw [integral_indicator hE, integral_const_mul]
    _ = ∫ ω, retirementSurvivalTerm P r α γ (t + 1) ω
          ∂markovChainMeasure P x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω ↦ by
        have hsurv :=
          threshold_survival_succ_eq P r α γ t ω
        dsimp [E, W]
        simp only [Set.indicator, Set.mem_setOf_eq,
          retirementSurvivalTerm]
        calc
          (if (t : ℕ∞) <
                gittinsRetirementThresholdTime P r α γ ω then
              α ^ (t + 1) *
                gittinsRetirementValue P r α γ (ω (t + 1))
            else 0) =
              α ^ (t + 1) *
                (if (t : ℕ∞) <
                    gittinsRetirementThresholdTime P r α γ ω then
                  gittinsRetirementValue P r α γ (ω (t + 1))
                else 0) := by
            split_ifs <;> simp
          _ = α ^ (t + 1) *
                (if ((t + 1 : ℕ) : ℕ∞) <
                    gittinsRetirementThresholdTime P r α γ ω then
                  gittinsRetirementValue P r α γ (ω (t + 1))
                else 0) :=
            congrArg (fun z : ℝ ↦ α ^ (t + 1) * z) hsurv.symm
          _ = if ((t + 1 : ℕ) : ℕ∞) <
                  gittinsRetirementThresholdTime P r α γ ω then
                α ^ (t + 1) *
                  gittinsRetirementValue P r α γ (ω (t + 1))
              else 0 := by
            split_ifs <;> simp

lemma integral_retirementSurvivalTerm_eq_net_add_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) {t : ℕ} (h1t : 1 ≤ t) :
    (∫ ω, retirementSurvivalTerm P r α γ t ω
        ∂markovChainMeasure P x) =
      (∫ ω, retirementNetTerm P r α γ t ω
        ∂markovChainMeasure P x) +
      ∫ ω, retirementSurvivalTerm P r α γ (t + 1) ω
        ∂markovChainMeasure P x := by
  have hS :=
    integrable_retirementSurvivalTerm
      P hr hα0 hα1 hint γ x t
  have hQ :=
    integrable_retirementNetTerm
      P hr hα0 hα1 hint γ x t
  have hpoint :
      retirementSurvivalTerm P r α γ t =
        fun ω ↦
          retirementNetTerm P r α γ t ω +
            retirementContinuationTerm P r α γ t ω := by
    funext ω
    exact retirementSurvivalTerm_eq_net_add_continuation
      P hr hα0 hα1 hint γ h1t ω
  have hC :
      Integrable
        (retirementContinuationTerm P r α γ t)
        (markovChainMeasure P x) := by
    rw [show retirementContinuationTerm P r α γ t =
        fun ω ↦
          retirementSurvivalTerm P r α γ t ω -
            retirementNetTerm P r α γ t ω by
          funext ω
          have hp := congrFun hpoint ω
          linarith]
    exact hS.sub hQ
  calc
    (∫ ω, retirementSurvivalTerm P r α γ t ω
        ∂markovChainMeasure P x) =
        ∫ ω,
          (retirementNetTerm P r α γ t ω +
            retirementContinuationTerm P r α γ t ω)
          ∂markovChainMeasure P x := by
      rw [hpoint]
    _ = (∫ ω, retirementNetTerm P r α γ t ω
          ∂markovChainMeasure P x) +
        ∫ ω, retirementContinuationTerm P r α γ t ω
          ∂markovChainMeasure P x :=
      integral_add hQ hC
    _ = (∫ ω, retirementNetTerm P r α γ t ω
          ∂markovChainMeasure P x) +
        ∫ ω, retirementSurvivalTerm P r α γ (t + 1) ω
          ∂markovChainMeasure P x := by
      rw [integral_retirementContinuationTerm_eq_survival_succ
        P hr hα0 hα1 hint γ x t]

lemma integral_markovChain_eval_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : Measurable f) (x : S) :
    (∫ ω, f (ω 0) ∂markovChainMeasure P x) = f x := by
  rw [markovChainMeasure_eq_traj_zero]
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hsm :
      AEStronglyMeasurable
        (fun ω : ℕ → S ↦ f (ω 0))
        (Kernel.traj (markovChainStep P) 0 x₀) :=
    (hf.comp (measurable_pi_apply 0)).aestronglyMeasurable
  rw [Kernel.integral_traj
    (X := fun _ : ℕ ↦ S) (κ := markovChainStep P) x₀ hsm]
  rw [show (fun ω : ℕ → S ↦
      f ((Function.updateFinset ω (Finset.Iic 0) x₀) 0)) =
        fun _ ↦ f x by
      funext ω
      simp [Function.updateFinset, x₀]]
  simp

lemma integrable_markovChain_eval_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ℝ) (hf : Measurable f) (x : S) :
    Integrable (fun ω : ℕ → S ↦ f (ω 0))
      (markovChainMeasure P x) := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  have hmap :
      Integrable f
        ((markovChainMeasure P x).map
          (fun ω : ℕ → S ↦ ω 0)) := by
    rw [markovChainMeasure_eq_traj_zero]
    rw [map_traj_eval_eq_trajectoryStateMarginal P 0 0 x₀]
    rw [trajectoryStateMarginal_zero]
    exact integrable_dirac' hf.stronglyMeasurable (by simp)
  exact (integrable_map_measure
    hf.aestronglyMeasurable
    (measurable_pi_apply 0).aemeasurable).1 hmap

lemma integral_retirementNet_zero_add_survival_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) :
    (∫ ω,
        retirementNetTerm P r α
          (gittinsIndex P r α x) 0 ω
        ∂markovChainMeasure P x) +
      (∫ ω,
        retirementSurvivalTerm P r α
          (gittinsIndex P r α x) 1 ω
        ∂markovChainMeasure P x) = 0 := by
  let γ : ℝ := gittinsIndex P r α x
  let W : S → ℝ :=
    gittinsRetirementValue P r α γ
  let f : S → ℝ :=
    fun y ↦ r y - γ + α * ∫ z, W z ∂P y
  have hWmeas : Measurable W :=
    measurable_gittinsRetirementValue_of_discounted
      P hr hα0 hα1 hint γ
  have hf : Measurable f :=
    (hr.sub measurable_const).add
      (measurable_const.mul
        hWmeas.stronglyMeasurable.integral_kernel.measurable)
  have hQ :=
    integrable_retirementNetTerm
      P hr hα0 hα1 hint γ x 0
  have hF :=
    integrable_markovChain_eval_zero P f hf x
  have hpoint :
      (fun ω : ℕ → S ↦
        retirementNetTerm P r α γ 0 ω +
          retirementContinuationTerm P r α γ 0 ω) =
        fun ω ↦ f (ω 0) := by
    funext ω
    have h0 :
        (0 : ℕ∞) <
          gittinsRetirementThresholdTime P r α γ ω :=
      lt_of_lt_of_le (by norm_num)
        (one_le_gittinsRetirementThresholdTime P r α γ ω)
    simp [retirementNetTerm, retirementContinuationTerm,
      h0, f, W]
  have hC :
      Integrable
        (retirementContinuationTerm P r α γ 0)
        (markovChainMeasure P x) := by
    rw [show retirementContinuationTerm P r α γ 0 =
        fun ω ↦ f (ω 0) -
          retirementNetTerm P r α γ 0 ω by
        funext ω
        have hp := congrFun hpoint ω
        linarith]
    exact hF.sub hQ
  change
    (∫ ω, retirementNetTerm P r α γ 0 ω
      ∂markovChainMeasure P x) +
      (∫ ω, retirementSurvivalTerm P r α γ 1 ω
        ∂markovChainMeasure P x) = 0
  rw [← integral_retirementContinuationTerm_eq_survival_succ
    P hr hα0 hα1 hint γ x 0]
  rw [← integral_add hQ hC]
  rw [hpoint]
  rw [integral_markovChain_eval_zero P f hf x]
  exact gittinsRetirementValue_fair_continuation
    P hr hα0 hα1 hint x

lemma truncatedStoppedSum_eq_sum_retirementNetTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α γ : ℝ)
    (N : ℕ) (ω : ℕ → S) :
    truncatedStoppedSum α (fun y ↦ r y - γ)
        (gittinsRetirementThresholdTime P r α γ) N ω =
      ∑ t ∈ Finset.range N,
        retirementNetTerm P r α γ t ω := by
  rfl

lemma integral_truncatedStoppedSum_eq_sum_retirementNetTerm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) (N : ℕ) :
    (∫ ω,
        truncatedStoppedSum α (fun y ↦ r y - γ)
          (gittinsRetirementThresholdTime P r α γ) N ω
        ∂markovChainMeasure P x) =
      ∑ t ∈ Finset.range N,
        ∫ ω, retirementNetTerm P r α γ t ω
          ∂markovChainMeasure P x := by
  rw [show (fun ω ↦
      truncatedStoppedSum α (fun y ↦ r y - γ)
        (gittinsRetirementThresholdTime P r α γ) N ω) =
      fun ω ↦ ∑ t ∈ Finset.range N,
        retirementNetTerm P r α γ t ω by
      funext ω
      exact truncatedStoppedSum_eq_sum_retirementNetTerm
        P r α γ N ω]
  exact integral_finsetSum (Finset.range N) fun t _ ↦
    integrable_retirementNetTerm
      P hr hα0 hα1 hint γ x t

theorem integral_truncatedStoppedSum_fair_eq_neg_survival
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    (∫ ω,
        truncatedStoppedSum α
          (fun y ↦ r y - gittinsIndex P r α x)
          (gittinsRetirementThresholdTime P r α
            (gittinsIndex P r α x)) (N + 1) ω
        ∂markovChainMeasure P x) =
      - ∫ ω,
          retirementSurvivalTerm P r α
            (gittinsIndex P r α x) (N + 1) ω
          ∂markovChainMeasure P x := by
  let γ : ℝ := gittinsIndex P r α x
  let Q : ℕ → ℝ := fun t ↦
    ∫ ω, retirementNetTerm P r α γ t ω
      ∂markovChainMeasure P x
  let V : ℕ → ℝ := fun t ↦
    ∫ ω, retirementSurvivalTerm P r α γ t ω
      ∂markovChainMeasure P x
  have hfirst : Q 0 + V 1 = 0 := by
    exact integral_retirementNet_zero_add_survival_one
      P hr hα0 hα1 hint x
  have hstep : ∀ t, 1 ≤ t → V t = Q t + V (t + 1) := by
    intro t ht
    exact integral_retirementSurvivalTerm_eq_net_add_succ
      P hr hα0 hα1 hint γ x ht
  have htel : ∀ n : ℕ,
      (∑ t ∈ Finset.range (n + 1), Q t) + V (n + 1) = 0 := by
    intro n
    induction n with
    | zero =>
        simpa using hfirst
    | succ n ih =>
        rw [show n + 1 + 1 = (n + 1) + 1 by omega]
        rw [Finset.sum_range_succ]
        have hs := hstep (n + 1) (by omega)
        linarith
  change
    (∫ ω,
        truncatedStoppedSum α (fun y ↦ r y - γ)
          (gittinsRetirementThresholdTime P r α γ) (N + 1) ω
        ∂markovChainMeasure P x) = - V (N + 1)
  rw [integral_truncatedStoppedSum_eq_sum_retirementNetTerm
    P hr hα0 hα1 hint γ x (N + 1)]
  have h := htel N
  dsimp [Q] at h ⊢
  linarith

theorem tendsto_integral_retirementSurvivalTerm_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (γ : ℝ) (x : S) :
    Tendsto
      (fun N ↦
        ∫ ω, retirementSurvivalTerm P r α γ N ω
          ∂markovChainMeasure P x)
      atTop (𝓝 0) := by
  let W : S → ℝ :=
    gittinsRetirementValue P r α γ
  have htail :
      Tendsto
        (fun N ↦ α ^ N *
          ∫ ω, W (ω N) ∂markovChainMeasure P x)
        atTop (𝓝 0) :=
    tendsto_discounted_gittinsRetirementValue_integral_zero
      P hr hα0 hα1 hint γ x
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N ↦ by
      apply integral_nonneg
      intro ω
      by_cases hs :
          (N : ℕ∞) <
            gittinsRetirementThresholdTime P r α γ ω
      · rw [retirementSurvivalTerm, if_pos hs]
        exact mul_nonneg (pow_nonneg hα0.le N)
          (gittinsRetirementValue_nonneg
            P hr hα0 hα1 hint γ (ω N))
      · rw [retirementSurvivalTerm, if_neg hs]
        rfl
  · exact Filter.Eventually.of_forall fun N ↦ by
      have hS :=
        integrable_retirementSurvivalTerm
          P hr hα0 hα1 hint γ x N
      have hW :=
        (integrable_gittinsRetirementValue_along_markov
          P hr hα0 hα1 hint γ x N).const_mul (α ^ N)
      calc
        (∫ ω, retirementSurvivalTerm P r α γ N ω
            ∂markovChainMeasure P x) ≤
            ∫ ω, α ^ N * W (ω N)
              ∂markovChainMeasure P x := by
          apply integral_mono hS hW
          intro ω
          by_cases hs :
              (N : ℕ∞) <
                gittinsRetirementThresholdTime P r α γ ω
          · simp [retirementSurvivalTerm, hs, W]
          · simp [retirementSurvivalTerm, hs,
              mul_nonneg (pow_nonneg hα0.le N)
                (gittinsRetirementValue_nonneg
                  P hr hα0 hα1 hint γ (ω N)), W]
        _ = α ^ N *
            ∫ ω, W (ω N) ∂markovChainMeasure P x := by
          rw [integral_const_mul]
  · exact htail

theorem integral_discountedStoppedSum_fair_threshold_eq_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) :
    (∫ ω,
        discountedStoppedSum α
          (fun y ↦ r y - gittinsIndex P r α x)
          (gittinsRetirementThresholdTime P r α
            (gittinsIndex P r α x)) ω
        ∂markovChainMeasure P x) = 0 := by
  let γ : ℝ := gittinsIndex P r α x
  let τ := gittinsRetirementThresholdTime P r α γ
  let A : ℕ → ℝ := fun N ↦
    ∫ ω,
      truncatedStoppedSum α (fun y ↦ r y - γ) τ N ω
        ∂markovChainMeasure P x
  have hτ :
      IsTrajStoppingTime τ :=
    gittinsRetirementThresholdTime_isStoppingTime
      P hr hα0 hα1 hint γ
  have hfull :
      Tendsto A atTop
        (𝓝 (∫ ω,
          discountedStoppedSum α (fun y ↦ r y - γ) τ ω
            ∂markovChainMeasure P x)) :=
    tendsto_integral_truncatedStoppedSum_sub_charge
      P hr hα0 hα1 hint x γ hτ
  have hsurv :
      Tendsto
        (fun N ↦
          ∫ ω, retirementSurvivalTerm P r α γ (N + 1) ω
            ∂markovChainMeasure P x)
        atTop (𝓝 0) :=
    (tendsto_integral_retirementSurvivalTerm_zero
      P hr hα0 hα1 hint γ x).comp
        (tendsto_add_atTop_nat 1)
  have hshiftZero :
      Tendsto (fun N ↦ A (N + 1)) atTop (𝓝 0) := by
    have hneg :
        Tendsto
          (fun N ↦ -
            ∫ ω, retirementSurvivalTerm P r α γ (N + 1) ω
              ∂markovChainMeasure P x)
          atTop (𝓝 0) := by
      simpa using hsurv.neg
    apply hneg.congr'
    exact Filter.Eventually.of_forall fun N ↦ by
      dsimp [A, τ, γ]
      exact (integral_truncatedStoppedSum_fair_eq_neg_survival
        P hr hα0 hα1 hint x N).symm
  have hshiftFull :
      Tendsto (fun N ↦ A (N + 1)) atTop
        (𝓝 (∫ ω,
          discountedStoppedSum α (fun y ↦ r y - γ) τ ω
            ∂markovChainMeasure P x)) :=
    (tendsto_add_atTop_iff_nat 1).2 hfull
  have hzero :
      (∫ ω,
        discountedStoppedSum α (fun y ↦ r y - γ) τ ω
          ∂markovChainMeasure P x) = 0 :=
    tendsto_nhds_unique hshiftFull hshiftZero
  exact hzero

theorem gittinsRetirementThresholdTime_stoppingRatio_eq_index
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) :
    (∫ ω,
        discountedStoppedSum α r
          (gittinsRetirementThresholdTime P r α
            (gittinsIndex P r α x)) ω
        ∂markovChainMeasure P x) /
      (∫ ω,
        discountedStoppedSum α (fun _ : S ↦ 1)
          (gittinsRetirementThresholdTime P r α
            (gittinsIndex P r α x)) ω
        ∂markovChainMeasure P x) =
      gittinsIndex P r α x := by
  let γ : ℝ := gittinsIndex P r α x
  let τ := gittinsRetirementThresholdTime P r α γ
  have hτ :
      IsTrajStoppingTime τ :=
    gittinsRetirementThresholdTime_isStoppingTime
      P hr hα0 hα1 hint γ
  have hτ1 : ∀ ω, 1 ≤ τ ω :=
    one_le_gittinsRetirementThresholdTime P r α γ
  have hden :
      0 < ∫ ω,
        discountedStoppedSum α (fun _ : S ↦ 1) τ ω
          ∂markovChainMeasure P x := by
    have hb :=
      (integral_discountedStoppedSum_one_bounds
        P hα0.le hα1 x hτ hτ1).1
    linarith
  have hnet :
      (∫ ω,
        discountedStoppedSum α (fun y ↦ r y - γ) τ ω
          ∂markovChainMeasure P x) = 0 :=
    integral_discountedStoppedSum_fair_threshold_eq_zero
      P hr hα0 hα1 hint x
  rw [integral_discountedStoppedSum_sub_charge
    P hr hα0.le hα1 hint x hτ] at hnet
  change
    (∫ ω, discountedStoppedSum α r τ ω
      ∂markovChainMeasure P x) /
      (∫ ω, discountedStoppedSum α (fun _ : S ↦ 1) τ ω
        ∂markovChainMeasure P x) = γ
  apply (div_eq_iff hden.ne').2
  linarith

example {S : Type*} [MeasurableSpace S] :
    Adapted (Filtration.piLE (X := fun _ : ℕ ↦ S))
      (fun t (ω : ℕ → S) ↦ ω t) := by
  intro t
  rw [Filtration.piLE_eq_comap_frestrictLe]
  change Measurable[MeasurableSpace.comap
    (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1) inferInstance]
      ((fun z : (i : Finset.Iic t) → S ↦ z ⟨t, Finset.mem_Iic.2 le_rfl⟩) ∘
        (fun (ω : ℕ → S) (i : Finset.Iic t) ↦ ω i.1))
  exact (measurable_pi_apply _).comp
    (comap_measurable _)

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



lemma measurable_truncateMarkovBanditHistory
    {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable
      (truncateMarkovBanditHistory :
        MarkovBanditHistory k S (n + 1) →
          MarkovBanditHistory k S n) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro t
    exact (measurable_pi_apply (Fin.castSucc t)).comp measurable_fst
  · exact measurable_fst.comp
      ((measurable_pi_apply (Fin.last n)).comp measurable_fst)

lemma truncateMarkovBanditHistory_snoc
    {k n : ℕ} {S : Type*}
    (h : MarkovBanditHistory k S n)
    (a : Fin k) (y : S) :
    truncateMarkovBanditHistory
      (Fin.snoc h.1 (h.2, a),
        Function.update h.2 a y) = h := by
  apply Prod.ext
  · simp [truncateMarkovBanditHistory]
  · simp [truncateMarkovBanditHistory]

lemma map_markovBanditMeasure_truncate
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    (markovBanditMeasure P π x (n + 1)).map
        truncateMarkovBanditHistory =
      markovBanditMeasure P π x n := by
  rw [markovBanditMeasure]
  rw [Measure.map_map]
  · rw [show
      truncateMarkovBanditHistory ∘
          (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦
            (Fin.snoc p.1.1 (p.1.2, p.2.1),
              Function.update p.1.2 p.2.1 p.2.2)) =
        Prod.fst by
        funext p
        exact truncateMarkovBanditHistory_snoc
          p.1 p.2.1 p.2.2]
    exact Measure.fst_compProd
      (markovBanditMeasure P π x n)
      (markovBanditStepKernel P π n)
  · exact measurable_truncateMarkovBanditHistory
  · exact measurable_markovBanditSnoc


@[simp] lemma currentHistoryPrevailingCharge_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (h : MarkovBanditHistory k S 0) (i : Fin k) :
    currentHistoryPrevailingCharge g 0 h i = g (h.2 i) :=
  rfl

theorem measurable_gittinsRetirementValue_joint
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) :
    Measurable (fun p : ℝ × S ↦
      gittinsRetirementValue P r α p.1 p.2) := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  have hG : 0 ≤ G :=
    tsum_nonneg fun t ↦ pow_nonneg hα0.le t
  change Measurable (Function.uncurry
    (fun γ y ↦ gittinsRetirementValue P r α γ y))
  apply measurable_uncurry_of_continuous_of_measurable
  · intro x
    have hLip : LipschitzWith (⟨G, hG⟩ : NNReal)
        (fun γ : ℝ ↦ gittinsRetirementValue P r α γ x) := by
      apply LipschitzWith.of_dist_le_mul
      intro γ δ
      simpa [Real.dist_eq, G, mul_comm] using
        gittinsRetirementValue_lipschitz_charge
          P hr hα0 hα1 hint x γ δ
    exact hLip.continuous
  · intro γ
    exact measurable_gittinsRetirementValue_of_discounted
      P hr hα0 hα1 hint γ

noncomputable def gittinsRetirementValueJoint
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (p : ℝ × S) : ℝ :=
  gittinsRetirementValue P r α p.1 p.2

lemma measurable_gittinsRetirementValueJoint
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) :
    Measurable (gittinsRetirementValueJoint P r α) := by
  exact measurable_gittinsRetirementValue_joint
    P hr hα0 hα1 hint

lemma measurable_currentHistoryPrevailingCharge
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    {g : S → ℝ} (hg : Measurable g) :
    ∀ (n : ℕ) (i : Fin k),
      Measurable (fun h : MarkovBanditHistory k S n ↦
        currentHistoryPrevailingCharge g n h i) := by
  intro n
  induction n with
  | zero =>
      intro i
      exact hg.comp ((measurable_pi_apply i).comp measurable_snd)
  | succ n ih =>
      intro i
      rw [show
        (fun h : MarkovBanditHistory k S (n + 1) ↦
          currentHistoryPrevailingCharge g (n + 1) h i) =
        fun h ↦ min
          (currentHistoryPrevailingCharge g n
            (truncateMarkovBanditHistory h) i)
          (g (h.2 i)) by rfl]
      exact ((ih i).comp measurable_truncateMarkovBanditHistory).inf'
        (hg.comp ((measurable_pi_apply i).comp measurable_snd))


set_option maxHeartbeats 800000 in
lemma measurable_currentGittinsRetirementPotential_coord
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (i : Fin k) :
    Measurable (fun h : MarkovBanditHistory k S n ↦
      gittinsRetirementValueJoint P r α
        (currentHistoryPrevailingCharge
          (gittinsIndex P r α) n h i, h.2 i)) := by
  have hcharge := measurable_currentHistoryPrevailingCharge
    (measurable_gittinsIndex_of_discounted
      P hr hα0 hα1 hint) n i
  have hstate : Measurable
      (fun h : MarkovBanditHistory k S n ↦ h.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  exact (measurable_gittinsRetirementValueJoint
    P hr hα0 hα1 hint).comp (hcharge.prodMk hstate)

noncomputable def currentGittinsRetirementPotentialM
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) : ℝ :=
  ∑ i : Fin k,
    gittinsRetirementValueJoint P r α
      (currentHistoryPrevailingCharge
        (gittinsIndex P r α) n h i, h.2 i)

lemma measurable_currentGittinsRetirementPotentialM
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) :
    Measurable (currentGittinsRetirementPotentialM
      (k := k) (n := n) P r α) := by
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_currentGittinsRetirementPotential_coord
    P hr hα0 hα1 hint i

private lemma discountedStoppedSum_abs_le_fullAbs
    {S : Type*} {α : ℝ} (hα0 : 0 ≤ α)
    (r : S → ℝ) (τ : (ℕ → S) → ℕ∞) (ω : ℕ → S)
    (hsum : Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|)) :
    |discountedStoppedSum α r τ ω| ≤
      ∑' t : ℕ, α ^ t * |r (ω t)| := by
  let f : ℕ → ℝ := fun t ↦
    if (t : ℕ∞) < τ ω then α ^ t * r (ω t) else 0
  have hf : Summable f := by
    apply Summable.of_norm_bounded hsum
    intro t
    by_cases ht : (t : ℕ∞) < τ ω
    · simp [f, ht, abs_of_nonneg hα0]
    · simp [f, ht, mul_nonneg
        (pow_nonneg hα0 t) (abs_nonneg _)]
  change |∑' t, f t| ≤ ∑' t : ℕ, α ^ t * |r (ω t)|
  calc
    |∑' t, f t| ≤ ∑' t, |f t| :=
      norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' t : ℕ, α ^ t * |r (ω t)| := by
      apply hf.norm.tsum_le_tsum
      · intro t
        by_cases ht : (t : ℕ∞) < τ ω
        · simp [f, ht, abs_of_nonneg hα0]
        · simp [f, ht, mul_nonneg
            (pow_nonneg hα0 t) (abs_nonneg _)]
      · exact hsum

private lemma measurable_discountedAbsSeries_multiarm
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|) := by
  apply Measurable.tsum
  intro t
  exact measurable_const.mul
    (by
      have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop)

lemma ae_summable_discountedAbsSeries_multiarm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hmeas : Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal
        (α ^ t * |r (ω t)|)) := by
    apply Measurable.ennreal_tsum
    intro t
    exact ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        (by
          have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
            hr.comp (measurable_pi_apply t)
          fun_prop))
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal
          (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top hmeas (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

private lemma integrable_discountedAbsSeries_multiarm
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|)
      (markovChainMeasure P x) := by
  have habs : Measurable (fun y ↦ |r y|) := by
    fun_prop
  have hintAbs : DiscountedRewardIntegrable P
      (fun y ↦ |r y|) α := by
    intro y
    simpa only [abs_abs] using hint y
  simpa [discountedStoppedSum] using
    (integrable_discountedStoppedSum P habs hα0 hintAbs x
      (top_isTrajStoppingTime (S := S)))

theorem abs_gittinsIndex_le_discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    |gittinsIndex P r α x| ≤
      discountedAbsoluteRewardValue P r α x := by
  let γ := gittinsIndex P r α x
  let τ := gittinsRetirementThresholdTime P r α γ
  let μ := markovChainMeasure P x
  let R : (ℕ → S) → ℝ := fun ω ↦
    ∑' t : ℕ, α ^ t * |r (ω t)|
  let num : ℝ := ∫ ω, discountedStoppedSum α r τ ω ∂μ
  let den : ℝ := ∫ ω,
    discountedStoppedSum α (fun _ : S ↦ 1) τ ω ∂μ
  have hτ : IsTrajStoppingTime τ :=
    gittinsRetirementThresholdTime_isStoppingTime
      P hr hα0 hα1 hint γ
  have hτ1 : ∀ ω, 1 ≤ τ ω :=
    one_le_gittinsRetirementThresholdTime P r α γ
  have hden1 : 1 ≤ den := by
    simpa [den, μ] using
      (integral_discountedStoppedSum_one_bounds
        P hα0.le hα1 x hτ hτ1).1
  have hden0 : 0 < den := lt_of_lt_of_le zero_lt_one hden1
  have hRint : Integrable R μ := by
    simpa [R, μ] using
      integrable_discountedAbsSeries_multiarm
        P hr hα0.le hint x
  have hnumInt : Integrable
      (discountedStoppedSum α r τ) μ := by
    simpa [μ] using
      integrable_discountedStoppedSum
        P hr hα0.le hint x hτ
  have hnumA : |num| ≤ discountedAbsoluteRewardValue P r α x := by
    calc
      |num| ≤ ∫ ω, |discountedStoppedSum α r τ ω| ∂μ := by
        simpa [num] using
          (abs_integral_le_integral_abs
            (μ := μ) (f := discountedStoppedSum α r τ))
      _ ≤ ∫ ω, R ω ∂μ := by
        apply integral_mono_ae hnumInt.abs hRint
        filter_upwards
          [ae_summable_discountedAbsSeries_multiarm
            P hr hα0.le hint x] with ω hsum
        exact discountedStoppedSum_abs_le_fullAbs
          hα0.le r τ ω hsum
      _ = discountedAbsoluteRewardValue P r α x := by
        rfl
  have hA0 : 0 ≤ discountedAbsoluteRewardValue P r α x := by
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  have hratio : num / den = γ := by
    simpa [num, den, μ, τ, γ] using
      gittinsRetirementThresholdTime_stoppingRatio_eq_index
        P hr hα0 hα1 hint x
  change |γ| ≤ discountedAbsoluteRewardValue P r α x
  rw [← hratio]
  rw [abs_div, abs_of_pos hden0]
  apply (div_le_iff₀ hden0).2
  nlinarith

theorem measurable_discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} :
    Measurable (discountedAbsoluteRewardValue P r α) := by
  rw [show discountedAbsoluteRewardValue P r α =
      fun x ↦ ∫ ω, (∑' t : ℕ, α ^ t * |r (ω t)|)
        ∂markovChainKernel P x by
    funext x
    rw [markovChainKernel_apply]
    rfl]
  exact (measurable_discountedAbsSeries_multiarm hr).stronglyMeasurable
    |>.integral_kernel.measurable

lemma map_markovChainMeasure_eval_one
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    (markovChainMeasure P x).map (fun ω : ℕ → S ↦ ω 1) =
      P x := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  rw [markovChainMeasure_eq_traj_zero]
  rw [map_traj_eval_eq_trajectoryStateMarginal P 0 1 x₀]
  rw [show 1 = 0 + 1 by omega]
  rw [trajectoryStateMarginal_succ,
    trajectoryStateMarginal_zero]
  exact Measure.dirac_bind P.measurable x

lemma integrable_discountedAbsoluteRewardValue_kernel
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (discountedAbsoluteRewardValue P r α) (P x) := by
  have htraj :=
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint x 1).1
  have hmap : Integrable (discountedAbsoluteRewardValue P r α)
      ((markovChainMeasure P x).map (fun ω : ℕ → S ↦ ω 1)) :=
    (integrable_map_measure
      (measurable_discountedAbsoluteRewardValue P hr).aestronglyMeasurable
      (measurable_pi_apply 1).aemeasurable).2 htraj
  rwa [map_markovChainMeasure_eval_one P x] at hmap

theorem discountedAbsoluteRewardValue_bellman
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    discountedAbsoluteRewardValue P r α x =
      |r x| + α * ∫ y,
        discountedAbsoluteRewardValue P r α y ∂P x := by
  let μ := markovChainMeasure P x
  let R : (ℕ → S) → ℝ := fun ω ↦
    ∑' t : ℕ, α ^ t * |r (ω t)|
  let F : (ℕ → S) → ℝ :=
    discountedAbsoluteRewardFuture r α 1
  have hRint : Integrable R μ := by
    simpa [R, μ] using integrable_discountedAbsSeries_multiarm
      P hr hα0.le hint x
  have hFint : Integrable F μ := by
    simpa [F, μ] using
      integrable_discountedAbsoluteRewardFuture_markov
        P hr hα0 hint x 1
  have hsplit : R =ᵐ[μ] fun ω ↦ |r (ω 0)| + α * F ω := by
    filter_upwards
      [ae_summable_discountedAbsSeries_multiarm
        P hr hα0.le hint x]
      with ω hsum
    dsimp [R, F, discountedAbsoluteRewardFuture]
    have hs := hsum.sum_add_tsum_nat_add 1
    calc
      (∑' t : ℕ, α ^ t * |r (ω t)|) =
          (∑ t ∈ Finset.range 1, α ^ t * |r (ω t)|) +
            ∑' t : ℕ, α ^ (t + 1) * |r (ω (t + 1))| := hs.symm
      _ = |r (ω 0)| + α *
          ∑' t : ℕ, α ^ t * |r (ω (1 + t))| := by
        simp only [Finset.sum_range_one, pow_zero, one_mul]
        congr 1
        rw [← tsum_mul_left]
        apply tsum_congr
        intro t
        rw [pow_succ]
        rw [Nat.add_comm t 1]
        ring
  have hEval :=
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint x 1).2
  have hmapInt :
      (∫ ω, discountedAbsoluteRewardValue P r α (ω 1) ∂μ) =
        ∫ y, discountedAbsoluteRewardValue P r α y ∂P x := by
    rw [← map_markovChainMeasure_eval_one P x]
    rw [integral_map (measurable_pi_apply 1).aemeasurable
      (measurable_discountedAbsoluteRewardValue P hr).aestronglyMeasurable]
  change (∫ ω, R ω ∂μ) =
    |r x| + α * ∫ y,
      discountedAbsoluteRewardValue P r α y ∂P x
  rw [integral_congr_ae hsplit]
  rw [integral_add
    (integrable_markovChain_eval_zero P (fun y ↦ |r y|) (by fun_prop) x)
    (hFint.const_mul α)]
  rw [integral_markovChain_eval_zero P (fun y ↦ |r y|) (by fun_prop) x]
  rw [integral_const_mul]
  rw [← hEval, hmapInt]

noncomputable def markovBanditAbsoluteStatePotential
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) : ℝ :=
  ∑ i : Fin k, discountedAbsoluteRewardValue P r α (h.2 i)

lemma measurable_markovBanditAbsoluteStatePotential
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ} :
    Measurable (markovBanditAbsoluteStatePotential
      (k := k) (n := n) P r α) := by
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact (measurable_discountedAbsoluteRewardValue P hr).comp
    ((measurable_pi_apply i).comp measurable_snd)

lemma markovBanditAbsoluteStatePotential_nonneg
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α)
    (h : MarkovBanditHistory k S n) :
    0 ≤ markovBanditAbsoluteStatePotential P r α h := by
  apply Finset.sum_nonneg
  intro i hi
  dsimp [discountedAbsoluteRewardValue]
  exact integral_nonneg fun ω ↦
    tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)

lemma markovBanditAbsoluteStatePotential_update
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) (a : Fin k) (y : S) :
    markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y) =
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
        discountedAbsoluteRewardValue P r α y := by
  rw [markovBanditAbsoluteStatePotential]
  let F : Fin k → ℝ := fun i ↦
    discountedAbsoluteRewardValue P r α
      ((Function.update h.2 a y) i)
  change (∑ i, F i) = _
  rw [← Finset.sum_erase_add Finset.univ F (Finset.mem_univ a)]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hia : i ≠ a := Finset.ne_of_mem_erase hi
    simp [F, Function.update, hia]
  · simp [F, Function.update]

lemma integrable_markovBanditAbsoluteStatePotential_step_action
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    Integrable (fun y ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y))
      (P (h.2 a)) := by
  rw [show (fun y ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)) =
    fun y ↦
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      discountedAbsoluteRewardValue P r α y by
    funext y
    exact markovBanditAbsoluteStatePotential_update P r α h a y]
  exact (integrable_const _).add
    (integrable_discountedAbsoluteRewardValue_kernel
      P hr hα0 hint (h.2 a))

lemma measurable_markovBanditAbsoluteStatePotential_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (h : MarkovBanditHistory k S n) :
    Measurable (fun q : Fin k × S ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1),
          Function.update h.2 q.1 q.2)) := by
  apply measurable_from_prod_countable_right
  intro a
  rw [show (fun y ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)) =
    fun y ↦
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      discountedAbsoluteRewardValue P r α y by
    funext y
    exact markovBanditAbsoluteStatePotential_update P r α h a y]
  exact measurable_const.add
    (measurable_discountedAbsoluteRewardValue P hr)

lemma integrable_markovBanditAbsoluteStatePotential_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n) :
    Integrable (fun q : Fin k × S ↦
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1),
          Function.update h.2 q.1 q.2))
      (markovBanditStepKernel P π n h) := by
  rw [markovBanditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    (measurable_markovBanditAbsoluteStatePotential_step
      P hr h).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    exact integrable_markovBanditAbsoluteStatePotential_step_action
      P hr hα0 hint h a
  · exact Integrable.of_finite

lemma markovBanditAbsoluteStatePotential_eq_inactive_add
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    markovBanditAbsoluteStatePotential P r α h =
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      discountedAbsoluteRewardValue P r α (h.2 a) := by
  rw [markovBanditAbsoluteStatePotential]
  exact (Finset.sum_erase_add Finset.univ _
    (Finset.mem_univ a)).symm

lemma integral_markovBanditAbsoluteStatePotential_step_action
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    (∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)) =
      (∑ i ∈ Finset.univ.erase a,
        discountedAbsoluteRewardValue P r α (h.2 i)) +
      ∫ y, discountedAbsoluteRewardValue P r α y ∂P (h.2 a) := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun y ↦
    markovBanditAbsoluteStatePotential_update P r α h a y)]
  rw [integral_add (integrable_const _)
    (integrable_discountedAbsoluteRewardValue_kernel
      P hr hα0 hint (h.2 a))]
  simp

lemma integral_markovBanditAbsoluteStatePotential_step_action_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (h : MarkovBanditHistory k S n) (a : Fin k) :
    (∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂P (h.2 a)) ≤
      (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h := by
  rw [integral_markovBanditAbsoluteStatePotential_step_action
    P hr hα0 hint h a]
  have hbell := discountedAbsoluteRewardValue_bellman
    P hr hα0 hint (h.2 a)
  have hsplit := markovBanditAbsoluteStatePotential_eq_inactive_add
    P r α h a
  have hA0 : 0 ≤ discountedAbsoluteRewardValue P r α (h.2 a) := by
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  have hI0 : 0 ≤ ∫ y,
      discountedAbsoluteRewardValue P r α y ∂P (h.2 a) :=
    integral_nonneg fun y ↦ by
      dsimp [discountedAbsoluteRewardValue]
      exact integral_nonneg fun ω ↦
        tsum_nonneg fun t ↦
          mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  have hrest0 : 0 ≤ ∑ i ∈ Finset.univ.erase a,
      discountedAbsoluteRewardValue P r α (h.2 i) := by
    apply Finset.sum_nonneg
    intro i hi
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)
  field_simp
  nlinarith [abs_nonneg (r (h.2 a))]

lemma integral_markovBanditAbsoluteStatePotential_step_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S)
    (h : MarkovBanditHistory k S n) :
    (∫ q,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, q.1), Function.update h.2 q.1 q.2)
      ∂markovBanditStepKernel P π n h) ≤
      (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h := by
  have hInt := integrable_markovBanditAbsoluteStatePotential_step
    P hr hα0 hint π h
  rw [markovBanditStepKernel]
  rw [ProbabilityTheory.integral_compProd hInt]
  let J : Fin k → ℝ := fun a ↦
    ∫ y,
      markovBanditAbsoluteStatePotential P r α
        (Fin.snoc h.1 (h.2, a), Function.update h.2 a y)
      ∂(P.comap
        (fun p : MarkovBanditHistory k S n × Fin k ↦ p.1.2 p.2)
        measurable_currentArmState) (h, a)
  have hleft : Integrable J (π.select n h) :=
    Integrable.of_finite
  have hright : Integrable (fun _ : Fin k ↦
      (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h)
      (π.select n h) := integrable_const _
  change (∫ a, J a ∂(π.select n h)) ≤
    (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h
  calc
    (∫ a, J a ∂(π.select n h)) ≤
        ∫ _a : Fin k,
          (1 + α⁻¹) * markovBanditAbsoluteStatePotential P r α h
          ∂(π.select n h) := by
      apply integral_mono hleft hright
      intro a
      dsimp [J]
      exact integral_markovBanditAbsoluteStatePotential_step_action_le
        P hr hα0 hint h a
    _ = _ := by simp

theorem integrable_markovBanditAbsoluteStatePotential
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ n : ℕ,
      Integrable (markovBanditAbsoluteStatePotential P r α)
        (markovBanditMeasure P π x n) := by
  intro n
  induction n with
  | zero =>
      rw [markovBanditMeasure]
      exact integrable_dirac'
        (measurable_markovBanditAbsoluteStatePotential
          (n := 0) P hr).stronglyMeasurable (by simp)
  | succ n ih =>
      rw [markovBanditMeasure]
      apply (integrable_map_measure
        (measurable_markovBanditAbsoluteStatePotential
          (n := n + 1) P hr).aestronglyMeasurable
        measurable_markovBanditSnoc.aemeasurable).2
      let μ := markovBanditMeasure P π x n
      let K := markovBanditStepKernel P π n
      let F : MarkovBanditHistory k S n × (Fin k × S) → ℝ :=
        fun p ↦ markovBanditAbsoluteStatePotential P r α
          (Fin.snoc p.1.1 (p.1.2, p.2.1),
            Function.update p.1.2 p.2.1 p.2.2)
      have hFmeas : Measurable F :=
        (measurable_markovBanditAbsoluteStatePotential
          (n := n + 1) P hr).comp measurable_markovBanditSnoc
      apply (Measure.integrable_compProd_iff
        hFmeas.aestronglyMeasurable).2
      constructor
      · exact Filter.Eventually.of_forall fun h ↦
          integrable_markovBanditAbsoluteStatePotential_step
            P hr hα0 hint π h
      · let C : ℝ := 1 + α⁻¹
        let G : MarkovBanditHistory k S n → ℝ := fun h ↦
          ∫ q, ‖F (h, q)‖ ∂K h
        have hGsm : StronglyMeasurable G := by
          exact hFmeas.norm.stronglyMeasurable
            |>.integral_kernel_prod_right'
        have hCB : Integrable (fun h : MarkovBanditHistory k S n ↦
            C * markovBanditAbsoluteStatePotential P r α h) μ := by
          exact ih.const_mul C
        apply hCB.mono' hGsm.aestronglyMeasurable
        exact Filter.Eventually.of_forall fun h ↦ by
          rw [show G h =
              ∫ q, F (h, q) ∂K h by
            dsimp [G]
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun q ↦ by
              change |F (h, q)| = F (h, q)
              exact abs_of_nonneg
                (markovBanditAbsoluteStatePotential_nonneg
                  P r hα0.le _)]
          dsimp [C, K, F]
          rw [abs_of_nonneg (integral_nonneg fun q ↦
            markovBanditAbsoluteStatePotential_nonneg P r hα0.le _)]
          exact integral_markovBanditAbsoluteStatePotential_step_le
            P hr hα0 hint π h

lemma integrable_discountedAbsoluteRewardValue_current
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) (i : Fin k) :
    Integrable (fun h : MarkovBanditHistory k S n ↦
      discountedAbsoluteRewardValue P r α (h.2 i))
      (markovBanditMeasure P π x n) := by
  have hB := integrable_markovBanditAbsoluteStatePotential
    P hr hα0 hint π x n
  apply hB.mono'
    ((measurable_discountedAbsoluteRewardValue P hr).comp
      ((measurable_pi_apply i).comp measurable_snd)
      |>.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun h ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · change discountedAbsoluteRewardValue P r α (h.2 i) ≤
        ∑ j : Fin k, discountedAbsoluteRewardValue P r α (h.2 j)
      exact Finset.single_le_sum
        (f := fun j : Fin k ↦
          discountedAbsoluteRewardValue P r α (h.2 j))
        (fun j _ ↦ by
          exact integral_nonneg fun ω ↦
            tsum_nonneg fun t ↦
              mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _))
        (Finset.mem_univ i)
    · unfold discountedAbsoluteRewardValue
      exact integral_nonneg fun ω ↦
        tsum_nonneg fun t ↦
          mul_nonneg (pow_nonneg hα0.le t) (abs_nonneg _)

lemma integrable_gittinsIndex_current
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) (i : Fin k) :
    Integrable (fun h : MarkovBanditHistory k S n ↦
      gittinsIndex P r α (h.2 i))
      (markovBanditMeasure P π x n) := by
  have hA := integrable_discountedAbsoluteRewardValue_current
    P hr hα0 hint π x n i
  apply hA.mono'
    ((measurable_gittinsIndex_of_discounted P hr hα0 hα1 hint).comp
      ((measurable_pi_apply i).comp measurable_snd)
      |>.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun h ↦
    abs_gittinsIndex_le_discountedAbsoluteRewardValue
      P hr hα0 hα1 hint (h.2 i)

theorem integrable_currentHistoryPrevailingCharge
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (i : Fin k) :
    ∀ n : ℕ,
      Integrable (fun h : MarkovBanditHistory k S n ↦
        currentHistoryPrevailingCharge
          (gittinsIndex P r α) n h i)
        (markovBanditMeasure P π x n) := by
  intro n
  induction n with
  | zero =>
      rw [markovBanditMeasure]
      exact integrable_dirac'
        ((measurable_currentHistoryPrevailingCharge
          (measurable_gittinsIndex_of_discounted
            P hr hα0 hα1 hint) 0 i).stronglyMeasurable) (by simp)
  | succ n ih =>
      let μ := markovBanditMeasure P π x (n + 1)
      let fprev : MarkovBanditHistory k S (n + 1) → ℝ := fun h ↦
        currentHistoryPrevailingCharge (gittinsIndex P r α) n
          (truncateMarkovBanditHistory h) i
      let fnew : MarkovBanditHistory k S (n + 1) → ℝ := fun h ↦
        gittinsIndex P r α (h.2 i)
      have hprev : Integrable fprev μ := by
        apply (integrable_map_measure
          (measurable_currentHistoryPrevailingCharge
            (measurable_gittinsIndex_of_discounted
              P hr hα0 hα1 hint) n i).aestronglyMeasurable
          measurable_truncateMarkovBanditHistory.aemeasurable).1
        rw [map_markovBanditMeasure_truncate P π x]
        exact ih
      have hnew : Integrable fnew μ :=
        integrable_gittinsIndex_current
          P hr hα0 hα1 hint π x (n + 1) i
      have hmin : Integrable (fun h ↦ min (fprev h) (fnew h)) μ := by
        have h := ((hprev.add hnew).sub (hprev.sub hnew).abs).const_mul (2 : ℝ)⁻¹
        apply h.congr
        exact Filter.Eventually.of_forall fun z ↦ by
          dsimp
          rw [min_def]
          split_ifs with hz
          · rw [abs_of_nonpos (sub_nonpos.mpr hz)]
            ring
          · rw [abs_of_pos (sub_pos.mpr (lt_of_not_ge hz))]
            ring
      simpa [μ, fprev, fnew, currentHistoryPrevailingCharge] using hmin

lemma integrable_currentGittinsRetirementPotential_coord
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) (i : Fin k) :
    Integrable (fun h : MarkovBanditHistory k S n ↦
      gittinsRetirementValueJoint P r α
        (currentHistoryPrevailingCharge
          (gittinsIndex P r α) n h i, h.2 i))
      (markovBanditMeasure P π x n) := by
  let G : ℝ := ∑' t : ℕ, α ^ t
  let A : MarkovBanditHistory k S n → ℝ := fun h ↦
    discountedAbsoluteRewardValue P r α (h.2 i)
  let C : MarkovBanditHistory k S n → ℝ := fun h ↦
    currentHistoryPrevailingCharge
      (gittinsIndex P r α) n h i
  have hA : Integrable A (markovBanditMeasure P π x n) :=
    integrable_discountedAbsoluteRewardValue_current
      P hr hα0 hint π x n i
  have hC : Integrable C (markovBanditMeasure P π x n) :=
    integrable_currentHistoryPrevailingCharge
      P hr hα0 hα1 hint π x i n
  have hbound : Integrable (fun h ↦ A h + G * |C h|)
      (markovBanditMeasure P π x n) :=
    hA.add (hC.abs.const_mul G)
  apply hbound.mono'
    (measurable_currentGittinsRetirementPotential_coord
      P hr hα0 hα1 hint i).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun h ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · dsimp [gittinsRetirementValueJoint]
      have hle := gittinsRetirementValue_le_absReward_add_charge
        P hr hα0 hα1 hint (C h) (h.2 i)
      simpa [A, G, mul_comm] using hle
    · exact gittinsRetirementValue_nonneg
        P hr hα0 hα1 hint (C h) (h.2 i)

theorem integrable_currentGittinsRetirementPotentialM
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S)
    (n : ℕ) :
    Integrable (currentGittinsRetirementPotentialM P r α)
      (markovBanditMeasure P π x n) := by
  apply integrable_finsetSum
  intro i hi
  exact integrable_currentGittinsRetirementPotential_coord
    P hr hα0 hα1 hint π x n i

end BanditAlgorithm

namespace BanditAlgorithm




@[simp] lemma stackPullCountBefore_zero
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) :
    stackPullCountBefore a i 0 = 0 := by
  simp [stackPullCountBefore]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




def markovBanditStackHistory
    {k n : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ ω i (stackPullCountBefore a i t), a t),
    fun i ↦ ω i (stackPullCountBefore a i n))

@[simp] lemma markovBanditStackHistory_zero
    {k : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    markovBanditStackHistory (n := 0) ω a =
      (fun t ↦ t.elim0, fun i ↦ ω i 0) := by
  apply Prod.ext
  · funext t
    exact Fin.elim0 t
  · funext i
    simp [markovBanditStackHistory]

noncomputable def markovBanditArmPrevailingChargeStack
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) : ℝ :=
  (Finset.range (u + 1)).inf'
    ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
    (fun v ↦ g (ω i v))

@[simp] lemma markovBanditArmPrevailingChargeStack_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) :
    markovBanditArmPrevailingChargeStack g ω i 0 = g (ω i 0) := by
  simp [markovBanditArmPrevailingChargeStack]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm



abbrev MarkovBanditStackSpace (k : ℕ) (S : Type*) :=
  Fin k → ℕ → S


noncomputable def markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) : Measure (MarkovBanditStackSpace k S) :=
  Measure.pi (fun i ↦ markovChainMeasure P (x i))

instance markovBanditStackMeasure.instIsProbabilityMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) :
    IsProbabilityMeasure (markovBanditStackMeasure P x) := by
  rw [markovBanditStackMeasure]
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [markovChainMeasure]
    infer_instance
  exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _

def finiteStackPullCountBefore
    {k n : ℕ} (a : Fin n → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  ∑ s : Fin n, if (s : ℕ) < t ∧ a s = i then 1 else 0

def markovBanditFiniteStackHistory
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ omega i (finiteStackPullCountBefore a i t), a t),
    fun i ↦ omega i (finiteStackPullCountBefore a i n))

abbrev MarkovBanditStackPrefixSpace
    (k : ℕ) (S : Type*) (m : Fin k → ℕ) :=
  ∀ i : Fin k, Finset.Iic (m i) → S

def markovBanditStackPrefixes
    {k : ℕ} {S : Type*} (m : Fin k → ℕ)
    (omega : MarkovBanditStackSpace k S) :
    MarkovBanditStackPrefixSpace k S m :=
  fun i t ↦ omega i t

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

def markovBanditStackPrefixCurrent
    {k : ℕ} {S : Type*} (m : Fin k → ℕ) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S m) : S :=
  q i ⟨m i, Finset.mem_Iic.2 le_rfl⟩

lemma measurable_markovBanditStackPrefixCurrent
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    Measurable (markovBanditStackPrefixCurrent (S := S) m i) :=
  (measurable_pi_apply _).comp (measurable_pi_apply i)

noncomputable def markovBanditStackPrefixStep
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (m : Fin k → ℕ) (i : Fin k) :
    Kernel (MarkovBanditStackPrefixSpace k S m) S :=
  P.comap (markovBanditStackPrefixCurrent m i)
    (measurable_markovBanditStackPrefixCurrent m i)

instance markovBanditStackPrefixStep.instIsMarkovKernel
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (m : Fin k → ℕ) (i : Fin k) :
    IsMarkovKernel (markovBanditStackPrefixStep P m i) := by
  rw [markovBanditStackPrefixStep]
  infer_instance

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

lemma finiteStackPullCountBefore_mono
    {k n : ℕ} (a : Fin n → Fin k) (i : Fin k)
    {s t : ℕ} (hst : s ≤ t) :
    finiteStackPullCountBefore a i s ≤
      finiteStackPullCountBefore a i t := by
  classical
  apply Finset.sum_le_sum
  intro u hu
  by_cases hs : (u : ℕ) < s ∧ a u = i
  · have ht : (u : ℕ) < t ∧ a u = i :=
      ⟨lt_of_lt_of_le hs.1 hst, hs.2⟩
    simp [hs, ht]
  · simp [hs]

def markovBanditPrefixHistoryBefore
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n))
    (t : Fin (n + 1)) : MarkovBanditHistory k S t :=
  (fun u ↦
      (fun i ↦ q i ⟨finiteStackPullCountBefore a i u,
        Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
          (Nat.le_trans (Nat.le_of_lt u.isLt) (Nat.le_of_lt_succ t.isLt)))⟩,
        a ⟨u, lt_of_lt_of_le u.isLt (Nat.le_of_lt_succ t.isLt)⟩),
    fun i ↦ q i ⟨finiteStackPullCountBefore a i t,
      Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
        (Nat.le_of_lt_succ t.isLt))⟩)

noncomputable def markovBanditActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n)) : ENNReal :=
  ∏ t : Fin n,
    (pi.select t) (markovBanditPrefixHistoryBefore a q t.castSucc) {a t}

noncomputable def markovBanditStackActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (omega : MarkovBanditStackSpace k S) : ENNReal :=
  markovBanditActionLikelihood pi a
    (markovBanditStackPrefixes
      (fun i ↦ finiteStackPullCountBefore a i n) omega)

noncomputable def markovBanditFixedActionHistoryMeasure
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) : Measure (MarkovBanditHistory k S n) :=
  ((markovBanditStackMeasure P x).withDensity
      (markovBanditStackActionLikelihood pi a)).map
    (fun omega ↦ markovBanditFiniteStackHistory omega a)

instance markovBanditFixedActionHistoryMeasure.instSFinite
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) :
    SFinite (markovBanditFixedActionHistoryMeasure P pi x a) := by
  rw [markovBanditFixedActionHistoryMeasure]
  infer_instance

noncomputable def markovBanditSelectMass
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (i : Fin k)
    (h : MarkovBanditHistory k S n) : ENNReal :=
  (pi.select n) h {i}

noncomputable def markovBanditFixedActionStepKernel
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    Kernel (MarkovBanditHistory k S n) (Fin k × S) :=
  ((P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)).withDensity
    (fun h _ ↦ markovBanditSelectMass pi i h)).map
      (fun y ↦ (i, y))

instance markovBanditFixedActionStepKernel.instIsSFiniteKernel
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    IsSFiniteKernel (markovBanditFixedActionStepKernel
      (n := n) P pi i) := by
  let K : Kernel (MarkovBanditHistory k S n) S :=
    P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)
  letI : IsSFiniteKernel (K.withDensity
      (fun h _ ↦ markovBanditSelectMass pi i h)) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity K (fun h _ ↦ by
      exact measure_ne_top ((pi.select n) h) {i})
  rw [markovBanditFixedActionStepKernel]
  infer_instance

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm


end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal


theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α) :
    ∀ n : ℕ,
      Measurable (BanditAlgorithm.currentGittinsRetirementPotential P r α :
        BanditAlgorithm.MarkovBanditHistory k S n → ℝ) ∧
      ∀ (π : BanditAlgorithm.MarkovBanditPolicy k S) (x : Fin k → S),
        Integrable (BanditAlgorithm.currentGittinsRetirementPotential P r α)
          (BanditAlgorithm.markovBanditMeasure P π x n) := by
  intro n
  constructor
  · change Measurable (BanditAlgorithm.currentGittinsRetirementPotentialM
      (k := k) (n := n) P r α)
    exact BanditAlgorithm.measurable_currentGittinsRetirementPotentialM
      P hr hα0 hα1 hint
  · intro π x
    change Integrable (BanditAlgorithm.currentGittinsRetirementPotentialM P r α)
      (BanditAlgorithm.markovBanditMeasure P π x n)
    exact BanditAlgorithm.integrable_currentGittinsRetirementPotentialM
      P hr hα0 hα1 hint π x n
