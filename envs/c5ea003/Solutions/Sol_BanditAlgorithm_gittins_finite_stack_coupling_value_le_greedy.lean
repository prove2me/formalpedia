-- Prove2me | solution 1 for BanditAlgorithm.gittins_finite_stack_coupling_value_le_greedy
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T16:58:05.121261+00:00
-- url     : https://prove2.me/submissions/96a06ce8-9080-4c77-b856-f695df78d7be

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
import Theorems.Thm_BanditAlgorithm_gittins_prevailing_charge_regular
import Theorems.Thm_BanditAlgorithm_discounted_charge_stack_interleaving_le_greedy_prefix

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm

theorem measurable_gittinsIndex_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) :
    Measurable (gittinsIndex P r α) :=
  (gittins_prevailing_charge_regular (k := 0)
    P hr hα0 hα1 hint).1

lemma integrable_selectedCurrentHistoryPrevailingCharge_step
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) :
    Integrable (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦
      currentHistoryPrevailingCharge
        (gittinsIndex P r α) n p.1 p.2.1)
      ((markovBanditMeasure P π x n).compProd
        (markovBanditStepKernel P π n)) :=
  (gittins_prevailing_charge_regular P hr hα0 hα1 hint).2.2 n π x

theorem discounted_sum_chargeStackInterleaving_le_greedy_before
    {k N : ℕ} {H : Fin k → ℕ → ℝ} {astar : ℕ → Fin k}
    (hH : ∀ i, Antitone (H i))
    (hastar : ∀ n, n < N → ∀ i,
      H i (stackPullCountBefore astar i n) ≤
        H (astar n) (stackPullCountBefore astar (astar n) n))
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (a : ℕ → Fin k) :
    (∑ n ∈ Finset.range N,
        α ^ n * chargeStackInterleaving H a n) ≤
      ∑ n ∈ Finset.range N,
        α ^ n * chargeStackInterleaving H astar n :=
  discounted_charge_stack_interleaving_le_greedy_prefix
    hH hastar hα0 hα1 a

end BanditAlgorithm

open MeasureTheory ProbabilityTheory
open Filter Topology

namespace BanditAlgorithm

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

def markovBanditHistoryStateAt
    {k n : ℕ} {S : Type*}
    (h : MarkovBanditHistory k S n) : Fin (n + 1) → Fin k → S :=
  Fin.snoc (fun t ↦ (h.1 t).1) h.2


@[simp] lemma currentHistoryPrevailingCharge_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (h : MarkovBanditHistory k S 0) (i : Fin k) :
    currentHistoryPrevailingCharge g 0 h i = g (h.2 i) :=
  rfl

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


def HasBanditStateUpdates
    {k n : ℕ} {S : Type*}
    (h : MarkovBanditHistory k S n) : Prop :=
  ∀ (t : Fin n) (i : Fin k), i ≠ (h.1 t).2 →
    markovBanditHistoryStateAt h t.succ i =
      markovBanditHistoryStateAt h t.castSucc i


def IsGreedyIndexHistory
    {k n : ℕ} {S : Type*}
    (g : S → ℝ) (h : MarkovBanditHistory k S n) : Prop :=
  ∀ (t : Fin n) (i : Fin k),
    g ((h.1 t).1 i) ≤ g ((h.1 t).1 ((h.1 t).2))

theorem currentHistoryPrevailingCharge_invariant
    {k n : ℕ} {S : Type*}
    (g : S → ℝ) (h : MarkovBanditHistory k S n)
    (hstate : HasBanditStateUpdates h)
    (hgreedy : IsGreedyIndexHistory g h)
    (a : Fin k) (ha : ∀ i : Fin k, g (h.2 i) ≤ g (h.2 a)) :
    (∀ i : Fin k,
      currentHistoryPrevailingCharge g n h i ≤
        currentHistoryPrevailingCharge g n h a) ∧
    (∀ i : Fin k, i ≠ a →
      currentHistoryPrevailingCharge g n h i = g (h.2 i)) := by
  induction n generalizing a with
  | zero =>
      constructor
      · intro i
        simpa using ha i
      · intro i hi
        rfl
  | succ n ih =>
      let p : MarkovBanditHistory k S n :=
        truncateMarkovBanditHistory h
      let b : Fin k := (h.1 (Fin.last n)).2
      have hpstate : HasBanditStateUpdates p := by
        intro t i hi
        have hi' : i ≠ (h.1 t.castSucc).2 := by
          simpa [p, truncateMarkovBanditHistory] using hi
        by_cases ht : (t : ℕ) + 1 < n
        · simpa [p, truncateMarkovBanditHistory,
            markovBanditHistoryStateAt, Fin.snoc, ht] using
              hstate t.castSucc i hi'
        · have hteq : (t : ℕ) + 1 = n := by omega
          have hs := hstate t.castSucc i hi'
          simp [markovBanditHistoryStateAt, Fin.snoc] at hs
          change
            (h.1 (⟨(t : ℕ) + 1, by omega⟩ : Fin (n + 1))).1 i =
              (h.1 t.castSucc).1 i at hs
          have hidx : (⟨(t : ℕ) + 1, by omega⟩ : Fin (n + 1)) =
              Fin.last n := by
            apply Fin.ext
            exact hteq
          rw [hidx] at hs
          simpa [p, truncateMarkovBanditHistory,
            markovBanditHistoryStateAt, Fin.snoc, ht, hteq] using hs
      have hpgreedy : IsGreedyIndexHistory g p := by
        intro t i
        simpa [p, truncateMarkovBanditHistory] using
          hgreedy t.castSucc i
      have hbgreedy : ∀ i : Fin k, g (p.2 i) ≤ g (p.2 b) := by
        intro i
        simpa [p, b, truncateMarkovBanditHistory] using
          hgreedy (Fin.last n) i
      obtain ⟨hprevmax, hprevfair⟩ :=
        ih p hpstate hpgreedy b hbgreedy
      have hsame : ∀ i : Fin k, i ≠ b → h.2 i = p.2 i := by
        intro i hi
        have hs := hstate (Fin.last n) i (by
          simpa [b] using hi)
        simpa [p, truncateMarkovBanditHistory,
          markovBanditHistoryStateAt, Fin.snoc] using hs
      have hcharge : ∀ i : Fin k,
          currentHistoryPrevailingCharge g (n + 1) h i =
            min (currentHistoryPrevailingCharge g n p i)
              (g (h.2 i)) := by
        intro i
        rfl
      by_cases hab : a = b
      · subst a
        constructor
        · intro i
          rw [hcharge i, hcharge b]
          exact min_le_min (hprevmax i) (ha i)
        · intro i hi
          have hs : h.2 i = p.2 i := hsame i hi
          rw [hcharge i, hs, hprevfair i hi]
          exact min_self _
      · have hnewb :
            currentHistoryPrevailingCharge g (n + 1) h b =
              g (h.2 b) := by
          rw [hcharge b, min_eq_right]
          calc
            g (h.2 b) ≤ g (h.2 a) := ha b
            _ = g (p.2 a) := by rw [hsame a hab]
            _ = currentHistoryPrevailingCharge g n p a :=
              (hprevfair a hab).symm
            _ ≤ currentHistoryPrevailingCharge g n p b :=
              hprevmax a
        have hnewa :
            currentHistoryPrevailingCharge g (n + 1) h a =
              g (h.2 a) := by
          rw [hcharge a, hsame a hab, hprevfair a hab]
          exact min_self _
        constructor
        · intro i
          rw [hnewa, hcharge i]
          exact le_trans (min_le_right _ _) (ha i)
        · intro i hia
          by_cases hib : i = b
          · subst i
            exact hnewb
          · rw [hcharge i, hsame i hib, hprevfair i hib]
            exact min_self _

end BanditAlgorithm

namespace BanditAlgorithm




@[simp] lemma stackPullCountBefore_zero
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) :
    stackPullCountBefore a i 0 = 0 := by
  simp [stackPullCountBefore]

lemma stackPullCountBefore_succ
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ) :
    stackPullCountBefore a i (n + 1) =
      stackPullCountBefore a i n + if a n = i then 1 else 0 := by
  rw [stackPullCountBefore, stackPullCountBefore,
    Finset.sum_range_succ]

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

lemma truncate_markovBanditStackHistory
    {k n : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    truncateMarkovBanditHistory
      (markovBanditStackHistory (n := n + 1) ω a) =
        markovBanditStackHistory (n := n) ω a := by
  apply Prod.ext
  · funext t
    rfl
  · rfl


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

lemma markovBanditArmPrevailingChargeStack_succ
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) :
    markovBanditArmPrevailingChargeStack g ω i (u + 1) =
      min (markovBanditArmPrevailingChargeStack g ω i u)
        (g (ω i (u + 1))) := by
  rw [markovBanditArmPrevailingChargeStack,
    markovBanditArmPrevailingChargeStack]
  apply le_antisymm
  · apply le_min
    · apply Finset.le_inf'
      intro v hv
      exact Finset.inf'_le _ (Finset.mem_range.2 <| by
        have := Finset.mem_range.1 hv
        omega)
    · exact Finset.inf'_le _ (Finset.mem_range.2 <| by omega)
  · apply Finset.le_inf'
    intro v hv
    have hv' := Finset.mem_range.1 hv
    by_cases hlast : v = u + 1
    · subst v
      exact min_le_right _ _
    · exact le_trans (min_le_left _ _)
        (Finset.inf'_le _ (Finset.mem_range.2 <| by omega))

lemma antitone_markovBanditArmPrevailingChargeStack
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) :
    Antitone (markovBanditArmPrevailingChargeStack g ω i) := by
  apply antitone_nat_of_succ_le
  intro u
  rw [markovBanditArmPrevailingChargeStack_succ]
  exact min_le_left _ _

lemma stackPullCountBefore_succ_selected
    {k : ℕ} (a : ℕ → Fin k) (n : ℕ) :
    stackPullCountBefore a (a n) (n + 1) =
      stackPullCountBefore a (a n) n + 1 := by
  simp [stackPullCountBefore_succ]

lemma stackPullCountBefore_succ_of_ne
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ)
    (hi : a n ≠ i) :
    stackPullCountBefore a i (n + 1) =
      stackPullCountBefore a i n := by
  simp [stackPullCountBefore_succ, hi]


theorem currentHistoryPrevailingCharge_markovBanditStackHistory
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    ∀ (n : ℕ) (i : Fin k),
      currentHistoryPrevailingCharge g n
          (markovBanditStackHistory (n := n) ω a) i =
        markovBanditArmPrevailingChargeStack g ω i
          (stackPullCountBefore a i n) := by
  intro n
  induction n with
  | zero =>
      intro i
      simp
  | succ n ih =>
      intro i
      rw [currentHistoryPrevailingCharge]
      rw [truncate_markovBanditStackHistory]
      rw [ih]
      change min
        (markovBanditArmPrevailingChargeStack g ω i
          (stackPullCountBefore a i n))
        (g (ω i (stackPullCountBefore a i (n + 1)))) = _
      by_cases hi : a n = i
      · subst i
        rw [stackPullCountBefore_succ_selected]
        exact (markovBanditArmPrevailingChargeStack_succ
          g ω (a n) (stackPullCountBefore a (a n) n)).symm
      · rw [stackPullCountBefore_succ_of_ne a i n hi]
        have hle : markovBanditArmPrevailingChargeStack g ω i
            (stackPullCountBefore a i n) ≤
            g (ω i (stackPullCountBefore a i n)) := by
          exact Finset.inf'_le _
            (Finset.mem_range.2 (Nat.lt_succ_self _))
        rw [min_eq_left hle]


theorem selectedCurrentHistoryPrevailingCharge_markovBanditStackHistory
    {k n : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    currentHistoryPrevailingCharge g n
        (markovBanditStackHistory (n := n) ω a) (a n) =
      chargeStackInterleaving
        (markovBanditArmPrevailingChargeStack g ω) a n := by
  exact currentHistoryPrevailingCharge_markovBanditStackHistory
    g ω a n (a n)


lemma hasBanditStateUpdates_markovBanditStackHistory
    {k n : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    HasBanditStateUpdates
      (markovBanditStackHistory (n := n) ω a) := by
  intro t i hi
  have hi' : a (t : ℕ) ≠ i := by
    intro hait
    apply hi
    simpa [markovBanditStackHistory] using hait.symm
  have hcount := stackPullCountBefore_succ_of_ne a i (t : ℕ) hi'
  by_cases ht : (t : ℕ) + 1 < n
  · simpa [markovBanditHistoryStateAt, Fin.snoc,
      markovBanditStackHistory, ht] using congrArg (ω i) hcount
  · have hteq : (t : ℕ) + 1 = n := by omega
    simpa [markovBanditHistoryStateAt, Fin.snoc,
      markovBanditStackHistory, ht, hteq] using congrArg (ω i) hcount

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

@[simp] lemma finiteStackPullCountBefore_restrict
    {k n : ℕ} (a : ℕ → Fin k) (i : Fin k) (t : ℕ)
    (ht : t ≤ n) :
    finiteStackPullCountBefore (fun s : Fin n ↦ a s) i t =
      stackPullCountBefore a i t := by
  classical
  rw [finiteStackPullCountBefore, stackPullCountBefore]
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ ↦ if s < t ∧ a s = i then 1 else 0) n]
  have hsubset : Finset.range t ⊆ Finset.range n := Finset.range_mono ht
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro s hs
    simp [Finset.mem_range.1 hs]
  · intro s hsn hst
    have hts : t ≤ s := by
      simpa [Finset.mem_range] using hst
    simp [not_lt_of_ge hts]


def markovBanditFiniteStackHistory
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ omega i (finiteStackPullCountBefore a i t), a t),
    fun i ↦ omega i (finiteStackPullCountBefore a i n))

lemma measurable_markovBanditFiniteStackHistory
    {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable (fun p : MarkovBanditStackSpace k S × (Fin n → Fin k) ↦
      markovBanditFiniteStackHistory p.1 p.2) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro t
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      change Measurable (fun p : MarkovBanditStackSpace k S ×
        (Fin n → Fin k) ↦ p.1 i (finiteStackPullCountBefore p.2 i t))
      exact measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply (finiteStackPullCountBefore a i t)).comp
          (measurable_pi_apply i)
    · exact (measurable_pi_apply t).comp measurable_snd
  · rw [measurable_pi_iff]
    intro i
    change Measurable (fun p : MarkovBanditStackSpace k S ×
      (Fin n → Fin k) ↦ p.1 i (finiteStackPullCountBefore p.2 i n))
    exact measurable_from_prod_countable_left fun a ↦
      (measurable_pi_apply (finiteStackPullCountBefore a i n)).comp
        (measurable_pi_apply i)

set_option maxHeartbeats 800000 in
lemma map_eval_zero_trajMeasure
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (mu0 : Measure (X 0)) [IsProbabilityMeasure mu0]
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (K n)] :
    (Kernel.trajMeasure mu0 K).map (fun z ↦ z 0) = mu0 := by
  have hevalMeas : Measurable (fun z : (n : ℕ) → X n ↦ z 0) :=
    measurable_pi_apply 0
  rw [Kernel.trajMeasure, Measure.map_comp _ _ hevalMeas]
  have hrestrict := Kernel.traj_map_frestrictLe_of_le
    (κ := K) (show 0 ≤ 0 from le_rfl)
  have heval : (fun z : (n : ℕ) → X n ↦ z 0) =
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) ∘
        (Preorder.frestrictLe 0) := by
    funext z
    rfl
  rw [heval]
  have hmap : (Kernel.traj K 0).map
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) ∘
        Preorder.frestrictLe 0) =
      ((Kernel.traj K 0).map (Preorder.frestrictLe 0)).map
        (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) := by
    exact Kernel.map_comp_right _
      (Preorder.measurable_frestrictLe 0)
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).measurable
  change ((Kernel.traj K 0).map
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) ∘
        Preorder.frestrictLe 0)) ∘ₘ
      (mu0.map (MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 ↦ X i)).symm) = mu0
  rw [hmap, hrestrict]
  rw [Kernel.deterministic_map
    (Preorder.measurable_frestrictLe₂ le_rfl)
    (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).measurable]
  change (fun q ↦ Measure.dirac
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i))
        (Preorder.frestrictLe₂ (show 0 ≤ 0 from le_rfl) q))) ∘ₘ
      (mu0.map (MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 ↦ X i)).symm) = mu0
  let e := MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)
  have hf : Measurable (fun q ↦
      e (Preorder.frestrictLe₂ (show 0 ≤ 0 from le_rfl) q)) :=
    e.measurable.comp (Preorder.measurable_frestrictLe₂ le_rfl)
  change (fun q ↦ Measure.dirac
      (e (Preorder.frestrictLe₂ (show 0 ≤ 0 from le_rfl) q))) ∘ₘ
      (mu0.map e.symm) = mu0
  rw [Measure.bind_dirac_eq_map _ hf]
  change (mu0.map e.symm).map e = mu0
  exact MeasurableEquiv.map_map_symm e


theorem map_markovChainMeasure_prefix_next
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (u : ℕ) :
    ((markovChainMeasure P x).map
      (Preorder.frestrictLe u)).compProd (markovChainStep P u) =
      (markovChainMeasure P x).map
        (fun omega ↦ (Preorder.frestrictLe u omega, omega (u + 1))) := by
  rw [markovChainMeasure]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

theorem map_markovBanditStackMeasure_initialStates
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    (markovBanditStackMeasure P x).map (fun omega ↦ fun i ↦ omega i 0) =
      Measure.dirac x := by
  have hi : ∀ i : Fin k,
      (markovChainMeasure P (x i)).map (fun omega ↦ omega 0) =
        Measure.dirac (x i) := by
    intro i
    rw [markovChainMeasure]
    exact map_eval_zero_trajMeasure _ _
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : ∀ i : Fin k, IsProbabilityMeasure
      ((markovChainMeasure P (x i)).map (fun omega ↦ omega 0)) :=
    fun _ ↦ Measure.isProbabilityMeasure_map
      (measurable_pi_apply 0).aemeasurable
  rw [markovBanditStackMeasure]
  change (Measure.pi (fun i ↦ markovChainMeasure P (x i))).map
      (fun omega i ↦ (fun path : ℕ → S ↦ path 0) (omega i)) =
    Measure.dirac x
  rw [Measure.pi_map_pi
    (fun _i ↦ (measurable_pi_apply 0).aemeasurable)]
  simp_rw [hi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.dirac_apply' x (MeasurableSet.univ_pi hs)]
  conv_rhs =>
    enter [2, i]
    rw [Measure.dirac_apply' (x i) (hs i)]
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · simp [Set.mem_pi, hx]
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_pi] using hx)]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Set.indicator, hi]

abbrev MarkovBanditStackPrefixSpace
    (k : ℕ) (S : Type*) (m : Fin k → ℕ) :=
  ∀ i : Fin k, Finset.Iic (m i) → S

def markovBanditStackPrefixes
    {k : ℕ} {S : Type*} (m : Fin k → ℕ)
    (omega : MarkovBanditStackSpace k S) :
    MarkovBanditStackPrefixSpace k S m :=
  fun i t ↦ omega i t

lemma measurable_markovBanditStackPrefixes
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) :
    Measurable (markovBanditStackPrefixes (S := S) m) := by
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro t
  exact (measurable_pi_apply (t : ℕ)).comp (measurable_pi_apply i)

theorem map_markovBanditStackMeasure_prefixes
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S)
    (m : Fin k → ℕ) :
    (markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes (S := S) m) =
      Measure.pi (fun i ↦
        (markovChainMeasure P (x i)).map (Preorder.frestrictLe (m i))) := by
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  rw [markovBanditStackMeasure]
  change (Measure.pi (fun i ↦ markovChainMeasure P (x i))).map
      (fun omega i ↦ Preorder.frestrictLe (m i) (omega i)) = _
  exact Measure.pi_map_pi
    (fun i ↦ (Preorder.measurable_frestrictLe (m i)).aemeasurable)


end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

def swapMiddle {A B C : Type*} : (A × B) × C → (A × C) × B :=
  fun q ↦ ((q.1.1, q.2), q.1.2)

lemma measurable_swapMiddle
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] :
    Measurable (swapMiddle (A := A) (B := B) (C := C)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

lemma kernel_const_compProd_comap_fst_eq_prod
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (nu : Measure B) [SFinite nu]
    (K : Kernel A C) [IsSFiniteKernel K] :
    (Kernel.const A nu) ⊗ₖ (K.comap Prod.fst measurable_fst) =
      (Kernel.const A nu) ×ₖ K := by
  ext a s hs
  rw [Kernel.compProd_apply hs]
  simp only [Kernel.comap_apply, Kernel.const_apply, Kernel.prod_apply]
  rw [Measure.prod_apply hs]

lemma kernel_prod_eq_compProd_const
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (K : Kernel A B) [IsSFiniteKernel K]
    (nu : Measure C) [SFinite nu] :
    K ×ₖ (Kernel.const A nu) =
      K ⊗ₖ ((Kernel.const (A × B) nu)) := by
  ext a s hs
  rw [Kernel.compProd_apply hs]
  simp only [Kernel.const_apply, Kernel.prod_apply]
  rw [Measure.prod_apply hs]

set_option maxHeartbeats 800000 in
theorem compProd_prod_comap_fst_reorder
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (mu : Measure A) [SFinite mu]
    (nu : Measure B) [SFinite nu]
    (K : Kernel A C) [IsSFiniteKernel K] :
    (((mu.prod nu).compProd (K.comap Prod.fst measurable_fst)).map
        (swapMiddle (A := A) (B := B) (C := C))) =
      (mu.compProd K).prod nu := by
  let KB : Kernel A B := Kernel.const A nu
  let eta : Kernel (A × B) C := K.comap Prod.fst measurable_fst
  have hk : KB ⊗ₖ eta = KB ×ₖ K := by
    exact kernel_const_compProd_comap_fst_eq_prod nu K
  have hswap : (KB ×ₖ K).map MeasurableEquiv.prodComm =
      K ×ₖ KB := Kernel.prodComm_prod
  have hright : K ×ₖ KB =
      K ⊗ₖ Kernel.const (A × C) nu := by
    exact kernel_prod_eq_compProd_const K nu
  rw [show mu.prod nu = mu ⊗ₘ KB by simp [KB]]
  rw [show (mu.compProd K).prod nu =
      (mu.compProd K) ⊗ₘ Kernel.const (A × C) nu by simp]
  change ((mu ⊗ₘ KB ⊗ₘ eta).map swapMiddle) =
    mu ⊗ₘ K ⊗ₘ Kernel.const (A × C) nu
  rw [← Measure.compProd_assoc]
  rw [hk]
  rw [← Measure.compProd_assoc]
  rw [← hright]
  rw [← hswap]
  rw [MeasureTheory.Measure.compProd_map
    MeasurableEquiv.prodComm.measurable]
  rw [Measure.map_map measurable_swapMiddle
      MeasurableEquiv.prodAssoc.symm.measurable,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (measurable_id.prodMap MeasurableEquiv.prodComm.measurable)]
  congr 1

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

noncomputable def swapMiddleEquiv
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] :
    ((A × B) × C) ≃ᵐ ((A × C) × B) :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl A).prodCongr MeasurableEquiv.prodComm) |>.trans
      MeasurableEquiv.prodAssoc.symm

lemma map_prodMap_equiv_compProd_comap
    {A D C : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [MeasurableSpace C]
    (e : A ≃ᵐ D) (mu : Measure A) [SFinite mu]
    (K : Kernel D C) [IsSFiniteKernel K] :
    (mu.compProd (K.comap e e.measurable)).map (Prod.map e id) =
      (mu.map e).compProd K := by
  ext s hs
  rw [Measure.map_apply (e.measurable.prodMap measurable_id) hs]
  rw [Measure.compProd_apply (hs.preimage
    (e.measurable.prodMap measurable_id))]
  rw [Measure.compProd_apply hs]
  simp only [Kernel.comap_apply]
  rw [MeasureTheory.lintegral_map'
    (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    e.measurable.aemeasurable]
  apply lintegral_congr
  intro a
  congr 1

lemma map_prodMap_compProd_comap
    {A D C : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [MeasurableSpace C]
    (f : A → D) (hf : Measurable f)
    (mu : Measure A) [SFinite mu]
    (K : Kernel D C) [IsSFiniteKernel K] :
    (mu.compProd (K.comap f hf)).map (Prod.map f id) =
      (mu.map f).compProd K := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs]
  rw [Measure.compProd_apply (hs.preimage
    (hf.prodMap measurable_id))]
  rw [Measure.compProd_apply hs]
  simp only [Kernel.comap_apply]
  rw [MeasureTheory.lintegral_map'
    (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    hf.aemeasurable]
  apply lintegral_congr
  intro a
  congr 1

lemma withDensity_compProd_left
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    (mu : Measure A) [SFinite mu]
    (K : Kernel A C) [IsSFiniteKernel K]
    (w : A → ENNReal) (hw : Measurable w) :
    (mu.withDensity w).compProd K =
      (mu.compProd K).withDensity (w ∘ Prod.fst) := by
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [lintegral_withDensity_eq_lintegral_mul mu hw
    (Kernel.measurable_kernel_prodMk_left hs)]
  rw [withDensity_apply (w ∘ Prod.fst) hs]
  rw [← MeasureTheory.lintegral_indicator hs]
  rw [Measure.lintegral_compProd]
  · apply lintegral_congr
    intro a
    simp only [Pi.mul_apply]
    rw [show (fun c ↦ s.indicator (w ∘ Prod.fst) (a, c)) =
        (Prod.mk a ⁻¹' s).indicator (fun _ ↦ w a) by
          rfl]
    rw [lintegral_indicator (measurable_prodMk_left hs)]
    simp
  · exact (hw.comp measurable_fst).indicator hs

lemma map_withDensity_comp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (f : A → B) (hf : Measurable f)
    (w : B → ENNReal) (hw : Measurable w) :
    (mu.withDensity (w ∘ f)).map f = (mu.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [withDensity_apply (w ∘ f) (hs.preimage hf)]
  rw [withDensity_apply w hs]
  rw [← lintegral_indicator (hs.preimage hf)]
  rw [← lintegral_indicator hs]
  rw [lintegral_map' (hw.indicator hs).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro a
  rfl

lemma withDensity_withDensity_of_measurable
    {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (w v : A → ENNReal)
    (hw : Measurable w) (hv : Measurable v) :
    (mu.withDensity w).withDensity v = mu.withDensity (w * v) := by
  ext s hs
  rw [withDensity_apply v hs]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul
    mu hw hv hs]
  rw [withDensity_apply (w * v) hs]

lemma map_withDensity_mul_comp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (f : A → B) (hf : Measurable f)
    (w : A → ENNReal) (hw : Measurable w)
    (v : B → ENNReal) (hv : Measurable v) :
    (mu.withDensity (w * (v ∘ f))).map f =
      ((mu.withDensity w).map f).withDensity v := by
  rw [← withDensity_withDensity_of_measurable mu w (v ∘ f)
    hw (hv.comp hf)]
  exact map_withDensity_comp (mu.withDensity w) f hf v hv

abbrev OtherArm {k : ℕ} (i : Fin k) := {j : Fin k // j ≠ i}
abbrev SelectedArm {k : ℕ} (i : Fin k) := {j : Fin k // j = i}

noncomputable def splitStackAt
    {k : ℕ} {S : Type*} [MeasurableSpace S] (i : Fin k) :
    MarkovBanditStackSpace k S ≃ᵐ
      ((ℕ → S) × (OtherArm i → ℕ → S)) := by
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  exact (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin k ↦ ℕ → S) (fun j ↦ j = i)).trans
    ((MeasurableEquiv.piUnique
      (fun _ : SelectedArm i ↦ ℕ → S)).prodCongr
        (MeasurableEquiv.refl (OtherArm i → ℕ → S)))

abbrev OtherPrefixSpace
    {k : ℕ} (S : Type*) (m : Fin k → ℕ) (i : Fin k) :=
  ∀ j : OtherArm i, Finset.Iic (m j) → S

noncomputable def splitStackPrefixAt
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    MarkovBanditStackPrefixSpace k S m ≃ᵐ
      ((Finset.Iic (m i) → S) × OtherPrefixSpace S m i) := by
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  exact (MeasurableEquiv.piEquivPiSubtypeProd
      (fun j : Fin k ↦ Finset.Iic (m j) → S)
      (fun j ↦ j = i)).trans
    ((MeasurableEquiv.piUnique
      (fun j : SelectedArm i ↦ Finset.Iic (m j) → S)).prodCongr
        (MeasurableEquiv.refl (OtherPrefixSpace S m i)))

theorem map_splitStackAt_markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (i : Fin k) :
    (markovBanditStackMeasure P x).map (splitStackAt (S := S) i) =
      (markovChainMeasure P (x i)).prod
        (Measure.pi (fun j : OtherArm i ↦
          markovChainMeasure P (x j))) := by
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : Fintype (SelectedArm i) := Subtype.fintype (fun j ↦ j = i)
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin k ↦ ℕ → S) (fun j ↦ j = i)
  let e1 := MeasurableEquiv.piUnique
    (fun _ : SelectedArm i ↦ ℕ → S)
  have hsplit :
      (Measure.pi (fun j : Fin k ↦ markovChainMeasure P (x j))).map e0 =
        (Measure.pi (fun j : SelectedArm i ↦
          markovChainMeasure P (x j))).prod
          (Measure.pi (fun j : OtherArm i ↦
            markovChainMeasure P (x j))) :=
    (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun j : Fin k ↦ markovChainMeasure P (x j))
      (fun j ↦ j = i)).map_eq
  have hsel :
      (Measure.pi (fun j : SelectedArm i ↦
        markovChainMeasure P (x j))).map e1 =
          markovChainMeasure P (x i) := by
    change (Measure.pi (fun j : SelectedArm i ↦
      markovChainMeasure P (x j))).map (Function.eval default) = _
    rw [Measure.pi_map_eval]
    simp [show ((default : SelectedArm i) : Fin k) = i from
      Subtype.property (default : SelectedArm i)]
  rw [markovBanditStackMeasure]
  change (Measure.pi (fun j : Fin k ↦
      markovChainMeasure P (x j))).map
        ((e1.prodCongr (MeasurableEquiv.refl
          (OtherArm i → ℕ → S))) ∘ e0) = _
  rw [← Measure.map_map
    (e1.prodCongr (MeasurableEquiv.refl
      (OtherArm i → ℕ → S))).measurable e0.measurable]
  rw [hsplit]
  change ((Measure.pi (fun j : SelectedArm i ↦
      markovChainMeasure P (x j))).prod
        (Measure.pi (fun j : OtherArm i ↦
          markovChainMeasure P (x j)))).map
      (Prod.map e1 id) = _
  rw [← Measure.map_prod_map _ _ e1.measurable measurable_id]
  rw [hsel, Measure.map_id]

theorem map_splitStackPrefixAt_markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k) :
    (markovBanditStackMeasure P x).map
        ((splitStackPrefixAt (S := S) m i) ∘
          markovBanditStackPrefixes m) =
      ((markovChainMeasure P (x i)).map
          (Preorder.frestrictLe (m i))).prod
        (Measure.pi (fun j : OtherArm i ↦
          (markovChainMeasure P (x j)).map
            (Preorder.frestrictLe (m j)))) := by
  let ν : ∀ j : Fin k, Measure (Finset.Iic (m j) → S) :=
    fun j ↦ (markovChainMeasure P (x j)).map
      (Preorder.frestrictLe (m j))
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : ∀ j : Fin k, IsProbabilityMeasure (ν j) := fun j ↦ by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (m j)).aemeasurable
  letI : Fintype (SelectedArm i) := Subtype.fintype (fun j ↦ j = i)
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun j : Fin k ↦ Finset.Iic (m j) → S) (fun j ↦ j = i)
  let e1 := MeasurableEquiv.piUnique
    (fun j : SelectedArm i ↦ Finset.Iic (m j) → S)
  have hsplit :
      (Measure.pi ν).map e0 =
        (Measure.pi (fun j : SelectedArm i ↦ ν j)).prod
          (Measure.pi (fun j : OtherArm i ↦ ν j)) :=
    (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      ν (fun j ↦ j = i)).map_eq
  have hsel :
      (Measure.pi (fun j : SelectedArm i ↦ ν j)).map e1 =
          ν i := by
    change (Measure.pi (fun j : SelectedArm i ↦ ν j)).map
      (Function.eval default) = _
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul]
    change ν (⟨i, rfl⟩ : SelectedArm i) = ν i
    rfl
  rw [← Measure.map_map
    (splitStackPrefixAt (S := S) m i).measurable
    (measurable_markovBanditStackPrefixes m)]
  rw [map_markovBanditStackMeasure_prefixes]
  change (Measure.pi ν).map
      ((e1.prodCongr (MeasurableEquiv.refl
        (OtherPrefixSpace S m i))) ∘ e0) = _
  rw [← Measure.map_map
    (e1.prodCongr (MeasurableEquiv.refl
      (OtherPrefixSpace S m i))).measurable e0.measurable]
  rw [hsplit]
  change ((Measure.pi (fun j : SelectedArm i ↦ ν j)).prod
      (Measure.pi (fun j : OtherArm i ↦ ν j))).map
        (Prod.map e1 id) = _
  rw [← Measure.map_prod_map _ _ e1.measurable measurable_id]
  rw [hsel, Measure.map_id]

def otherStackPrefixes
    {k : ℕ} {S : Type*} (m : Fin k → ℕ) (i : Fin k)
    (omega : OtherArm i → ℕ → S) : OtherPrefixSpace S m i :=
  fun j t ↦ omega j t

lemma measurable_otherStackPrefixes
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    Measurable (otherStackPrefixes (S := S) m i) := by
  rw [measurable_pi_iff]
  intro j
  rw [measurable_pi_iff]
  intro t
  exact (measurable_pi_apply (t : ℕ)).comp (measurable_pi_apply j)

theorem map_markovBanditStackMeasure_selected_prefix_next_other
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k) :
    (markovBanditStackMeasure P x).map (fun omega ↦
        ((Preorder.frestrictLe (m i) (omega i), omega i (m i + 1)),
          fun j : OtherArm i ↦
            Preorder.frestrictLe (m j) (omega j))) =
      ((markovChainMeasure P (x i)).map (fun path ↦
          (Preorder.frestrictLe (m i) path, path (m i + 1)))).prod
        (Measure.pi (fun j : OtherArm i ↦
          (markovChainMeasure P (x j)).map
            (Preorder.frestrictLe (m j)))) := by
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : IsProbabilityMeasure
      (Measure.pi (fun j : OtherArm i ↦
        markovChainMeasure P (x j))) := by infer_instance
  let f : (ℕ → S) → ((Finset.Iic (m i) → S) × S) :=
    fun path ↦ (Preorder.frestrictLe (m i) path, path (m i + 1))
  let g : (OtherArm i → ℕ → S) → OtherPrefixSpace S m i :=
    otherStackPrefixes m i
  have hf : Measurable f :=
    (Preorder.measurable_frestrictLe (m i)).prodMk
      (measurable_pi_apply (m i + 1))
  have hg : Measurable g := measurable_otherStackPrefixes m i
  rw [show (fun omega : MarkovBanditStackSpace k S ↦
      ((Preorder.frestrictLe (m i) (omega i), omega i (m i + 1)),
        fun j : OtherArm i ↦
          Preorder.frestrictLe (m j) (omega j))) =
      Prod.map f g ∘ splitStackAt (S := S) i by rfl]
  rw [← Measure.map_map (hf.prodMap hg) (splitStackAt (S := S) i).measurable]
  rw [map_splitStackAt_markovBanditStackMeasure]
  rw [← Measure.map_prod_map _ _ hf hg]
  congr 1
  change (Measure.pi (fun j : OtherArm i ↦
      markovChainMeasure P (x j))).map
        (fun omega (j : OtherArm i) ↦
          Preorder.frestrictLe (m j) (omega j)) = _
  exact Measure.pi_map_pi
    (fun j ↦ (Preorder.measurable_frestrictLe (m j)).aemeasurable)

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

noncomputable def splitStackPrefixNextAt
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    (MarkovBanditStackPrefixSpace k S m × S) ≃ᵐ
      (((Finset.Iic (m i) → S) × S) × OtherPrefixSpace S m i) :=
  ((splitStackPrefixAt (S := S) m i).prodCongr
    (MeasurableEquiv.refl S)).trans swapMiddleEquiv

theorem markovBanditStackMeasure_prefix_transition
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k) :
    ((markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes (S := S) m)).compProd
          (markovBanditStackPrefixStep P m i) =
      (markovBanditStackMeasure P x).map (fun omega ↦
        (markovBanditStackPrefixes m omega, omega i (m i + 1))) := by
  let E := splitStackPrefixAt (S := S) m i
  let K : Kernel
      ((Finset.Iic (m i) → S) × OtherPrefixSpace S m i) S :=
    (markovChainStep P (m i)).comap Prod.fst measurable_fst
  let μ := (markovChainMeasure P (x i)).map
    (Preorder.frestrictLe (m i))
  let ν := Measure.pi (fun j : OtherArm i ↦
    (markovChainMeasure P (x j)).map
      (Preorder.frestrictLe (m j)))
  let M := (markovBanditStackMeasure P x).map
    (markovBanditStackPrefixes (S := S) m)
  let F := splitStackPrefixNextAt (S := S) m i
  letI : IsProbabilityMeasure (markovChainMeasure P (x i)) := by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (m i)).aemeasurable
  letI : ∀ j : OtherArm i,
      IsProbabilityMeasure ((markovChainMeasure P (x j)).map
        (Preorder.frestrictLe (m j))) := fun j ↦ by
    letI : IsProbabilityMeasure (markovChainMeasure P (x j)) := by
      rw [← markovChainKernel_apply]
      infer_instance
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (m j)).aemeasurable
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hstep : markovBanditStackPrefixStep P m i =
      K.comap E E.measurable := by
    rfl
  have hbase : M.map E = μ.prod ν := by
    dsimp [M, μ, ν]
    rw [Measure.map_map E.measurable
      (measurable_markovBanditStackPrefixes m)]
    exact map_splitStackPrefixAt_markovBanditStackMeasure P x m i
  have hleft :
      (M.compProd (markovBanditStackPrefixStep P m i)).map F =
        (μ.compProd (markovChainStep P (m i))).prod ν := by
    rw [hstep]
    change (M.compProd (K.comap E E.measurable)).map
        (swapMiddleEquiv ∘ Prod.map E id) = _
    rw [← Measure.map_map swapMiddleEquiv.measurable
      (E.measurable.prodMap measurable_id)]
    rw [map_prodMap_equiv_compProd_comap E M K]
    rw [hbase]
    exact compProd_prod_comap_fst_reorder μ ν
      (markovChainStep P (m i))
  have hright :
      ((markovBanditStackMeasure P x).map (fun omega ↦
          (markovBanditStackPrefixes m omega, omega i (m i + 1)))).map F =
        (μ.compProd (markovChainStep P (m i))).prod ν := by
    rw [Measure.map_map F.measurable
      ((measurable_markovBanditStackPrefixes m).prodMk
        ((measurable_pi_apply (m i + 1)).comp
          (measurable_pi_apply i)))]
    change (markovBanditStackMeasure P x).map (fun omega ↦
        ((Preorder.frestrictLe (m i) (omega i), omega i (m i + 1)),
          fun j : OtherArm i ↦
            Preorder.frestrictLe (m j) (omega j))) = _
    rw [map_markovBanditStackMeasure_selected_prefix_next_other]
    rw [map_markovChainMeasure_prefix_next]
  apply F.map_measurableEquiv_injective
  rw [hleft, hright]

theorem markovBanditStackMeasure_weighted_prefix_transition
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k)
    (w : MarkovBanditStackPrefixSpace k S m → ENNReal)
    (hw : Measurable w) :
    (((markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes (S := S) m)).withDensity w).compProd
          (markovBanditStackPrefixStep P m i) =
      ((markovBanditStackMeasure P x).map (fun omega ↦
        (markovBanditStackPrefixes m omega, omega i (m i + 1)))).withDensity
          (w ∘ Prod.fst) := by
  rw [withDensity_compProd_left]
  rw [markovBanditStackMeasure_prefix_transition]
  exact hw

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

def markovBanditPrefixHistory
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n)) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ q i ⟨finiteStackPullCountBefore a i t,
        Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
          (Nat.le_of_lt t.isLt))⟩,
        a t),
    fun i ↦ q i ⟨finiteStackPullCountBefore a i n,
      Finset.mem_Iic.2 le_rfl⟩)

lemma measurable_markovBanditPrefixHistory
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (a : Fin n → Fin k) :
    Measurable (markovBanditPrefixHistory (S := S) a) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro t
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply _).comp (measurable_pi_apply i)
    · exact measurable_const
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply _).comp (measurable_pi_apply i)

lemma markovBanditPrefixHistory_stackPrefixes
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k) :
    markovBanditPrefixHistory a
        (markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n) omega) =
      markovBanditFiniteStackHistory omega a := by
  rfl

def markovBanditActionPrefix
    {k n : ℕ} (a : Fin (n + 1) → Fin k) : Fin n → Fin k :=
  fun t ↦ a t.castSucc

def markovBanditLastAction
    {k n : ℕ} (a : Fin (n + 1) → Fin k) : Fin k :=
  a (Fin.last n)

lemma finiteStackPullCountBefore_snoc_old
    {k n : ℕ} (a : Fin n → Fin k) (j i : Fin k) :
    finiteStackPullCountBefore (Fin.snoc a i) j n =
      finiteStackPullCountBefore a j n := by
  let b : ℕ → Fin k := fun t ↦
    if h : t < n then a ⟨t, h⟩ else i
  have ha : (fun t : Fin n ↦ b t) = a := by
    funext t
    simp [b, t.isLt]
  have has : (fun t : Fin (n + 1) ↦ b t) = Fin.snoc a i := by
    funext t
    by_cases ht : (t : ℕ) < n
    · simp only [b, dif_pos ht, Fin.snoc, ht, Fin.castLE]
      congr 1
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      simp [b, Fin.snoc]
  calc
    finiteStackPullCountBefore (Fin.snoc a i) j n =
        finiteStackPullCountBefore (fun t : Fin (n + 1) ↦ b t) j n := by
          rw [has]
    _ = stackPullCountBefore b j n :=
      finiteStackPullCountBefore_restrict b j n (Nat.le_succ n)
    _ = finiteStackPullCountBefore (fun t : Fin n ↦ b t) j n :=
      (finiteStackPullCountBefore_restrict b j n le_rfl).symm
    _ = finiteStackPullCountBefore a j n := by rw [ha]

lemma finiteStackPullCountBefore_snoc_before
    {k n : ℕ} (a : Fin n → Fin k) (j i : Fin k)
    (s : ℕ) (hs : s ≤ n) :
    finiteStackPullCountBefore (Fin.snoc a i) j s =
      finiteStackPullCountBefore a j s := by
  let b : ℕ → Fin k := fun t ↦
    if h : t < n then a ⟨t, h⟩ else i
  have ha : (fun t : Fin n ↦ b t) = a := by
    funext t
    simp [b, t.isLt]
  have has : (fun t : Fin (n + 1) ↦ b t) = Fin.snoc a i := by
    funext t
    by_cases ht : (t : ℕ) < n
    · simp only [b, dif_pos ht, Fin.snoc, ht]
      congr 1
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      simp [b, Fin.snoc]
  calc
    finiteStackPullCountBefore (Fin.snoc a i) j s =
        finiteStackPullCountBefore (fun t : Fin (n + 1) ↦ b t) j s := by
          rw [has]
    _ = stackPullCountBefore b j s :=
      finiteStackPullCountBefore_restrict b j s (hs.trans (Nat.le_succ n))
    _ = finiteStackPullCountBefore (fun t : Fin n ↦ b t) j s :=
      (finiteStackPullCountBefore_restrict b j s hs).symm
    _ = finiteStackPullCountBefore a j s := by rw [ha]

lemma finiteStackPullCountBefore_snoc_succ
    {k n : ℕ} (a : Fin n → Fin k) (j i : Fin k) :
    finiteStackPullCountBefore (Fin.snoc a i) j (n + 1) =
      finiteStackPullCountBefore a j n + if i = j then 1 else 0 := by
  let b : ℕ → Fin k := fun t ↦
    if h : t < n then a ⟨t, h⟩ else i
  have ha : (fun t : Fin n ↦ b t) = a := by
    funext t
    simp [b, t.isLt]
  have has : (fun t : Fin (n + 1) ↦ b t) = Fin.snoc a i := by
    funext t
    by_cases ht : (t : ℕ) < n
    · simp only [b, dif_pos ht, Fin.snoc, ht, Fin.castLE]
      congr 1
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      simp [b, Fin.snoc]
  calc
    finiteStackPullCountBefore (Fin.snoc a i) j (n + 1) =
        finiteStackPullCountBefore (fun t : Fin (n + 1) ↦ b t) j (n + 1) := by
          rw [has]
    _ = stackPullCountBefore b j (n + 1) :=
      finiteStackPullCountBefore_restrict b j (n + 1) le_rfl
    _ = stackPullCountBefore b j n + if b n = j then 1 else 0 := by
      rw [stackPullCountBefore_succ]
    _ = finiteStackPullCountBefore (fun t : Fin n ↦ b t) j n +
        if i = j then 1 else 0 := by
      rw [finiteStackPullCountBefore_restrict b j n le_rfl]
      simp [b]
    _ = finiteStackPullCountBefore a j n + if i = j then 1 else 0 := by
      rw [ha]

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

lemma measurable_markovBanditPrefixHistoryBefore
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (a : Fin n → Fin k) (t : Fin (n + 1)) :
    Measurable (markovBanditPrefixHistoryBefore (S := S) a · t) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro u
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply _).comp (measurable_pi_apply i)
    · exact measurable_const
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply _).comp (measurable_pi_apply i)

noncomputable def markovBanditActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n)) : ENNReal :=
  ∏ t : Fin n,
    (pi.select t) (markovBanditPrefixHistoryBefore a q t.castSucc) {a t}

lemma measurable_markovBanditActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k) :
    Measurable (markovBanditActionLikelihood pi a) := by
  apply Finset.measurable_prod
  intro t ht
  exact ((pi.select t).measurable_coe (MeasurableSet.singleton (a t))).comp
    (measurable_markovBanditPrefixHistoryBefore a t.castSucc)

def markovBanditSnocOldPrefix
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))) :
    MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore a j n) :=
  fun j u ↦ q j ⟨u, Finset.mem_Iic.2 <|
    le_trans (Finset.mem_Iic.1 u.property) <| by
      calc
        finiteStackPullCountBefore a j n ≤
            finiteStackPullCountBefore a j n + if i = j then 1 else 0 :=
          Nat.le_add_right _ _
        _ = finiteStackPullCountBefore (Fin.snoc a i) j (n + 1) :=
          (finiteStackPullCountBefore_snoc_succ a j i).symm⟩

lemma markovBanditPrefixHistoryBefore_snoc_castSucc
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1)))
    (t : Fin n) :
    markovBanditPrefixHistoryBefore (Fin.snoc a i) q t.castSucc.castSucc =
      markovBanditPrefixHistoryBefore a
        (markovBanditSnocOldPrefix a i q) t.castSucc := by
  apply Prod.ext
  · funext u
    apply Prod.ext
    · funext j
      simp only [markovBanditPrefixHistoryBefore,
        markovBanditSnocOldPrefix]
      congr 2
      exact finiteStackPullCountBefore_snoc_before a j i u
        (by omega)
    · simp only [markovBanditPrefixHistoryBefore]
      have hu : (u : ℕ) < n := lt_trans u.isLt t.isLt
      simp [Fin.snoc, hu]
  · funext j
    simp only [markovBanditPrefixHistoryBefore,
      markovBanditSnocOldPrefix]
    congr 2
    exact finiteStackPullCountBefore_snoc_before a j i t
      (Nat.le_of_lt t.isLt)

lemma markovBanditPrefixHistoryBefore_snoc_last
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))) :
    markovBanditPrefixHistoryBefore (Fin.snoc a i) q (Fin.last n).castSucc =
      markovBanditPrefixHistory a (markovBanditSnocOldPrefix a i q) := by
  apply Prod.ext
  · funext u
    apply Prod.ext
    · funext j
      simp only [markovBanditPrefixHistoryBefore,
        markovBanditPrefixHistory, markovBanditSnocOldPrefix]
      congr 2
      exact finiteStackPullCountBefore_snoc_before a j i u
        (Nat.le_of_lt u.isLt)
    · simp only [markovBanditPrefixHistoryBefore,
        markovBanditPrefixHistory]
      have hu : (u : ℕ) < n := u.isLt
      simp [Fin.snoc, hu]
  · funext j
    simp only [markovBanditPrefixHistoryBefore,
      markovBanditPrefixHistory, markovBanditSnocOldPrefix]
    congr 2
    exact finiteStackPullCountBefore_snoc_old a j i

lemma markovBanditActionLikelihood_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))) :
    markovBanditActionLikelihood pi (Fin.snoc a i) q =
      markovBanditActionLikelihood pi a (markovBanditSnocOldPrefix a i q) *
        (pi.select n)
          (markovBanditPrefixHistory a (markovBanditSnocOldPrefix a i q)) {i} := by
  rw [markovBanditActionLikelihood, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t ht
    rw [Fin.snoc_castSucc]
    rw [markovBanditPrefixHistoryBefore_snoc_castSucc]
    rfl
  · rw [Fin.snoc_last]
    rw [markovBanditPrefixHistoryBefore_snoc_last]
    rfl

noncomputable def markovBanditStackActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (omega : MarkovBanditStackSpace k S) : ENNReal :=
  markovBanditActionLikelihood pi a
    (markovBanditStackPrefixes
      (fun i ↦ finiteStackPullCountBefore a i n) omega)

lemma measurable_markovBanditStackActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k) :
    Measurable (markovBanditStackActionLikelihood pi a) :=
  (measurable_markovBanditActionLikelihood pi a).comp
    (measurable_markovBanditStackPrefixes _)

lemma markovBanditSnocOldPrefix_stackPrefixes
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditSnocOldPrefix a i
        (markovBanditStackPrefixes
          (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))
          omega) =
      markovBanditStackPrefixes
        (fun j ↦ finiteStackPullCountBefore a j n) omega := by
  rfl

lemma markovBanditStackActionLikelihood_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditStackActionLikelihood pi (Fin.snoc a i) omega =
      markovBanditStackActionLikelihood pi a omega *
        (pi.select n) (markovBanditFiniteStackHistory omega a) {i} := by
  rw [markovBanditStackActionLikelihood,
    markovBanditActionLikelihood_snoc]
  rw [markovBanditSnocOldPrefix_stackPrefixes]
  rw [markovBanditPrefixHistory_stackPrefixes]
  rfl

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

lemma markovBanditFixedActionHistoryMeasure_eq_prefix
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) :
    markovBanditFixedActionHistoryMeasure P pi x a =
      (((markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n))).withDensity
            (markovBanditActionLikelihood pi a)).map
        (markovBanditPrefixHistory a) := by
  rw [markovBanditFixedActionHistoryMeasure]
  rw [show (fun omega ↦ markovBanditFiniteStackHistory omega a) =
      markovBanditPrefixHistory a ∘
        markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n) by
        funext omega
        exact (markovBanditPrefixHistory_stackPrefixes omega a).symm]
  rw [← Measure.map_map (measurable_markovBanditPrefixHistory a)
    (measurable_markovBanditStackPrefixes _)]
  congr 1
  exact map_withDensity_comp
    (markovBanditStackMeasure P x)
    (markovBanditStackPrefixes
      (fun i ↦ finiteStackPullCountBefore a i n))
    (measurable_markovBanditStackPrefixes _)
    (markovBanditActionLikelihood pi a)
    (measurable_markovBanditActionLikelihood pi a)

lemma markovBanditFixedActionHistoryMeasure_zero
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditFixedActionHistoryMeasure P pi x
        (fun t : Fin 0 ↦ t.elim0) =
      markovBanditMeasure P pi x 0 := by
  rw [markovBanditFixedActionHistoryMeasure]
  have hone : markovBanditStackActionLikelihood pi
      (fun t : Fin 0 ↦ t.elim0) = fun _ ↦ 1 := by
    funext omega
    simp [markovBanditStackActionLikelihood,
      markovBanditActionLikelihood]
  rw [hone]
  change ((markovBanditStackMeasure P x).withDensity
      (1 : MarkovBanditStackSpace k S → ENNReal)).map
        (fun omega ↦ markovBanditFiniteStackHistory omega
          (fun t : Fin 0 ↦ t.elim0)) = _
  rw [withDensity_one]
  let f : MarkovBanditStackSpace k S → MarkovBanditHistory k S 0 :=
    fun omega ↦ markovBanditFiniteStackHistory omega
      (fun t : Fin 0 ↦ t.elim0)
  let eval0 : MarkovBanditStackSpace k S → Fin k → S :=
    fun omega i ↦ omega i 0
  let mk0 : (Fin k → S) → MarkovBanditHistory k S 0 :=
    fun y ↦ (fun t : Fin 0 ↦ t.elim0, y)
  have heval0 : Measurable eval0 := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply 0).comp (measurable_pi_apply i)
  have hmk0 : Measurable mk0 :=
    (measurable_pi_lambda _ fun t ↦ t.elim0).prodMk measurable_id
  change (markovBanditStackMeasure P x).map f = _
  rw [show f = mk0 ∘ eval0 by
    funext omega
    apply Prod.ext
    · funext t
      exact Fin.elim0 t
    · rfl]
  rw [← Measure.map_map hmk0 heval0]
  rw [map_markovBanditStackMeasure_initialStates]
  rw [Measure.map_dirac]
  rfl

def markovBanditHistorySnocFixed
    {k n : ℕ} {S : Type*} (i : Fin k)
    (p : MarkovBanditHistory k S n × S) :
    MarkovBanditHistory k S (n + 1) :=
  (Fin.snoc p.1.1 (p.1.2, i), Function.update p.1.2 i p.2)

lemma measurable_markovBanditHistorySnocFixed
    {k n : ℕ} {S : Type*} [MeasurableSpace S] (i : Fin k) :
    Measurable (markovBanditHistorySnocFixed (n := n) (S := S) i) := by
  exact measurable_markovBanditSnoc.comp
    (measurable_fst.prodMk
      (measurable_const.prodMk measurable_snd))

lemma markovBanditFiniteStackHistory_snoc
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditFiniteStackHistory omega (Fin.snoc a i) =
      markovBanditHistorySnocFixed i
        (markovBanditFiniteStackHistory omega a,
          omega i (finiteStackPullCountBefore a i n + 1)) := by
  apply Prod.ext
  · funext t
    by_cases ht : (t : ℕ) < n
    · apply Prod.ext
      · funext j
        simp only [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed, Fin.snoc, ht, dite_true]
        change omega j (finiteStackPullCountBefore (Fin.snoc a i) j t) =
          omega j (finiteStackPullCountBefore a j t)
        rw [finiteStackPullCountBefore_snoc_before a j i t
          (Nat.le_of_lt ht)]
      · simp [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed, Fin.snoc, ht]
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      apply Prod.ext
      · funext j
        simp only [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed, Fin.snoc_last]
        change omega j (finiteStackPullCountBefore (Fin.snoc a i) j n) =
          omega j (finiteStackPullCountBefore a j n)
        rw [finiteStackPullCountBefore_snoc_old]
      · simp [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed]
  · funext j
    simp only [markovBanditFiniteStackHistory,
      markovBanditHistorySnocFixed]
    rw [finiteStackPullCountBefore_snoc_succ]
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji, Ne.symm hji]

noncomputable def markovBanditSelectMass
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (i : Fin k)
    (h : MarkovBanditHistory k S n) : ENNReal :=
  (pi.select n) h {i}

lemma measurable_markovBanditSelectMass
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    Measurable (markovBanditSelectMass (n := n) pi i) :=
  (pi.select n).measurable_coe (MeasurableSet.singleton i)

theorem markovBanditFixedActionHistoryMeasure_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditFixedActionHistoryMeasure P pi x (Fin.snoc a i) =
      (((markovBanditFixedActionHistoryMeasure P pi x a).withDensity
          (markovBanditSelectMass pi i)).compProd
        (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
          ((measurable_pi_apply i).comp measurable_snd))).map
        (markovBanditHistorySnocFixed i) := by
  let m : Fin k → ℕ := fun j ↦ finiteStackPullCountBefore a j n
  let pref := markovBanditStackPrefixes (S := S) m
  let hist := markovBanditPrefixHistory (S := S) a
  let M := (markovBanditStackMeasure P x).map pref
  let w := markovBanditActionLikelihood pi a
  let v := markovBanditSelectMass (n := n) pi i
  let W : MarkovBanditStackPrefixSpace k S m → ENNReal :=
    w * (v ∘ hist)
  have hpref : Measurable pref := measurable_markovBanditStackPrefixes m
  have hhist : Measurable hist := measurable_markovBanditPrefixHistory a
  have hw : Measurable w := measurable_markovBanditActionLikelihood pi a
  have hv : Measurable v := measurable_markovBanditSelectMass pi i
  have hW : Measurable W := hw.mul (hv.comp hhist)
  have hfixed : markovBanditFixedActionHistoryMeasure P pi x a =
      (M.withDensity w).map hist := by
    simpa [M, m, pref, hist, w] using
      markovBanditFixedActionHistoryMeasure_eq_prefix P pi x a
  have hkernel :
      (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
        ((measurable_pi_apply i).comp measurable_snd)).comap hist hhist =
        markovBanditStackPrefixStep P m i := by
    rfl
  have hweighted := markovBanditStackMeasure_weighted_prefix_transition
    P x m i W hW
  rw [hfixed]
  rw [← map_withDensity_mul_comp M hist hhist w hw v hv]
  rw [← map_prodMap_compProd_comap hist hhist
    (M.withDensity W)
    (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd))]
  rw [Measure.map_map
    (measurable_markovBanditHistorySnocFixed i)
    (hhist.prodMap measurable_id)]
  rw [hkernel]
  rw [hweighted]
  rw [← map_withDensity_comp]
  rw [Measure.map_map
    ((measurable_markovBanditHistorySnocFixed i).comp
      (hhist.prodMap measurable_id))
    (hpref.prodMk
      ((measurable_pi_apply (m i + 1)).comp (measurable_pi_apply i)))]
  · rw [markovBanditFixedActionHistoryMeasure]
    congr 1
    · funext omega
      exact markovBanditFiniteStackHistory_snoc omega a i
    · congr 1
      funext omega
      rw [markovBanditStackActionLikelihood_snoc]
      rfl
  · exact (hpref.prodMk
      ((measurable_pi_apply (m i + 1)).comp (measurable_pi_apply i)))
  · exact hW.comp measurable_fst

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

theorem markovBanditStepKernel_eq_sum_fixedAction
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) :
    markovBanditStepKernel P pi n =
      ∑ i : Fin k, markovBanditFixedActionStepKernel P pi i := by
  ext h s hs
  rw [markovBanditStepKernel, Kernel.compProd_apply hs]
  rw [Kernel.finsetSum_apply' Finset.univ
    (fun i : Fin k ↦ markovBanditFixedActionStepKernel P pi i) h s]
  rw [← Measure.sum_smul_dirac (pi.select n h)]
  rw [lintegral_sum_measure]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_smul_measure]
  rw [lintegral_dirac']
  · rw [markovBanditFixedActionStepKernel]
    simp only [smul_eq_mul]
    rw [Kernel.map_apply
      ((P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
        ((measurable_pi_apply i).comp measurable_snd)).withDensity
          (fun h _ ↦ markovBanditSelectMass pi i h))
      (f := fun y : S ↦ (i, y))
      (measurable_const.prodMk measurable_id) h]
    have hf : Measurable (fun y : S ↦ (i, y)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_apply hf hs]
    have hd : Measurable (Function.uncurry
        (fun h : MarkovBanditHistory k S n ↦
          fun _ : S ↦ markovBanditSelectMass pi i h)) :=
      (measurable_markovBanditSelectMass pi i).comp measurable_fst
    rw [Kernel.withDensity_apply'
      (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
        ((measurable_pi_apply i).comp measurable_snd)) hd]
    rw [setLIntegral_const]
    simp [markovBanditSelectMass, Kernel.comap_apply,
      mul_comm]
  · exact Kernel.measurable_kernel_prodMk_left' hs h

def markovBanditHistorySnocGeneral
    {k n : ℕ} {S : Type*}
    (p : MarkovBanditHistory k S n × (Fin k × S)) :
    MarkovBanditHistory k S (n + 1) :=
  (Fin.snoc p.1.1 (p.1.2, p.2.1),
    Function.update p.1.2 p.2.1 p.2.2)

lemma measurable_markovBanditHistorySnocGeneral
    {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable (markovBanditHistorySnocGeneral (k := k) (n := n) (S := S)) :=
  measurable_markovBanditSnoc

theorem compProd_fixedActionStepKernel_map_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (mu : Measure (MarkovBanditHistory k S n))
    [SFinite mu] (i : Fin k) :
    (mu.compProd (markovBanditFixedActionStepKernel P pi i)).map
        markovBanditHistorySnocGeneral =
      (((mu.withDensity (markovBanditSelectMass pi i)).compProd
        (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
          ((measurable_pi_apply i).comp measurable_snd))).map
        (markovBanditHistorySnocFixed i)) := by
  let K : Kernel (MarkovBanditHistory k S n) S :=
    P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)
  let v := markovBanditSelectMass (n := n) pi i
  let pairI : S → Fin k × S := fun y ↦ (i, y)
  have hv : Measurable v := measurable_markovBanditSelectMass pi i
  have hpair : Measurable pairI := measurable_const.prodMk measurable_id
  have hd : Measurable (Function.uncurry (fun h : MarkovBanditHistory k S n ↦
      fun _ : S ↦ v h)) := hv.comp measurable_fst
  letI : IsSFiniteKernel (K.withDensity (fun h _ ↦ v h)) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity K (fun h _ ↦ by
      exact measure_ne_top ((pi.select n) h) {i})
  rw [markovBanditFixedActionStepKernel]
  rw [Measure.compProd_map hpair]
  rw [Measure.compProd_withDensity hd]
  change Measure.map markovBanditHistorySnocGeneral
      (Measure.map (Prod.map id pairI)
        ((mu.compProd K).withDensity (v ∘ Prod.fst))) =
    Measure.map (markovBanditHistorySnocFixed i)
      ((mu.withDensity v).compProd K)
  rw [← withDensity_compProd_left mu K v hv]
  rw [Measure.map_map measurable_markovBanditHistorySnocGeneral
    (measurable_id.prodMap hpair)]
  congr 1

theorem compProd_markovBanditStepKernel_map_snoc_eq_sum_fixed
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S)
    (mu : Measure (MarkovBanditHistory k S n)) [SFinite mu] :
    (mu.compProd (markovBanditStepKernel P pi n)).map
        markovBanditHistorySnocGeneral =
      ∑ i : Fin k,
        (((mu.withDensity (markovBanditSelectMass pi i)).compProd
          (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
            ((measurable_pi_apply i).comp measurable_snd))).map
          (markovBanditHistorySnocFixed i)) := by
  rw [markovBanditStepKernel_eq_sum_fixedAction]
  rw [← Kernel.sum_fintype]
  rw [Measure.compProd_sum_right]
  rw [Measure.map_sum
    measurable_markovBanditHistorySnocGeneral.aemeasurable]
  rw [Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  exact compProd_fixedActionStepKernel_map_snoc P pi mu i

theorem markovBanditMeasure_eq_sum_fixedActionHistoryMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ n : ℕ, markovBanditMeasure P pi x n =
      ∑ a : Fin n → Fin k,
        markovBanditFixedActionHistoryMeasure P pi x a := by
  intro n
  induction n with
  | zero =>
      have h0 := markovBanditFixedActionHistoryMeasure_zero P pi x
      simpa only [Fintype.sum_unique] using h0.symm
  | succ n ih =>
      rw [markovBanditMeasure]
      change ((markovBanditMeasure P pi x n).compProd
        (markovBanditStepKernel P pi n)).map
          markovBanditHistorySnocGeneral = _
      rw [ih]
      rw [← Measure.sum_fintype]
      rw [Measure.compProd_sum_left]
      rw [Measure.map_sum
        measurable_markovBanditHistorySnocGeneral.aemeasurable]
      rw [Measure.sum_fintype]
      simp_rw [compProd_markovBanditStepKernel_map_snoc_eq_sum_fixed]
      simp_rw [← markovBanditFixedActionHistoryMeasure_snoc]
      rw [← Fintype.sum_prod_type']
      let e : ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) :=
        Equiv.prodComm _ _ |>.trans (Fin.snocEquiv (fun _ ↦ Fin k))
      exact Fintype.sum_equiv e _ _ (fun q ↦ by
        change markovBanditFixedActionHistoryMeasure P pi x
            (Fin.snoc q.1 q.2) =
          markovBanditFixedActionHistoryMeasure P pi x (e q)
        rfl)

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm


theorem sum_markovBanditStackActionLikelihood
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S) :
    ∀ n : ℕ, ∑ a : Fin n → Fin k,
      markovBanditStackActionLikelihood pi a omega = 1 := by
  intro n
  induction n with
  | zero => simp [markovBanditStackActionLikelihood,
      markovBanditActionLikelihood]
  | succ n ih =>
      let e : ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) :=
        Equiv.prodComm _ _ |>.trans (Fin.snocEquiv (fun _ ↦ Fin k))
      rw [← e.sum_comp]
      change (∑ q : (Fin n → Fin k) × Fin k,
        markovBanditStackActionLikelihood pi (Fin.snoc q.1 q.2) omega) = 1
      rw [Fintype.sum_prod_type'
        (fun a : Fin n → Fin k ↦ fun i : Fin k ↦
          markovBanditStackActionLikelihood pi (Fin.snoc a i) omega)]
      change (∑ a : Fin n → Fin k, ∑ i : Fin k,
        markovBanditStackActionLikelihood pi (Fin.snoc a i) omega) = 1
      simp_rw [markovBanditStackActionLikelihood_snoc]
      calc
        (∑ a : Fin n → Fin k, ∑ i : Fin k,
            markovBanditStackActionLikelihood pi a omega *
              (pi.select n) (markovBanditFiniteStackHistory omega a) {i}) =
            ∑ a : Fin n → Fin k,
              markovBanditStackActionLikelihood pi a omega * 1 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_sum]
          congr 1
          simpa using MeasureTheory.Measure.sum_measure_singleton
            (s := Finset.univ)
            ((pi.select n) (markovBanditFiniteStackHistory omega a))
        _ = 1 := by simpa using ih

lemma sum_markovBanditStackActionLikelihood_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) :
    ∑ i : Fin k,
      markovBanditStackActionLikelihood pi (Fin.snoc a i) omega =
        markovBanditStackActionLikelihood pi a omega := by
  simp_rw [markovBanditStackActionLikelihood_snoc]
  rw [← Finset.mul_sum]
  have hone : ∑ i : Fin k,
      (pi.select n) (markovBanditFiniteStackHistory omega a) {i} = 1 := by
    simpa using MeasureTheory.Measure.sum_measure_singleton
      (s := Finset.univ)
      ((pi.select n) (markovBanditFiniteStackHistory omega a))
  rw [hone, mul_one]

theorem sum_withDensity_stackActionLikelihood_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) :
    ∑ i : Fin k, (markovBanditStackMeasure P x).withDensity
        (markovBanditStackActionLikelihood pi (Fin.snoc a i)) =
      (markovBanditStackMeasure P x).withDensity
        (markovBanditStackActionLikelihood pi a) := by
  rw [← Measure.sum_fintype]
  rw [← withDensity_tsum]
  · congr 1
    funext omega
    rw [tsum_fintype]
    simpa only [Finset.sum_apply] using
      sum_markovBanditStackActionLikelihood_snoc pi omega a
  · intro i
    exact measurable_markovBanditStackActionLikelihood pi (Fin.snoc a i)


lemma gittinsPolicy_select_singleton_eq_zero_of_not_max
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (pi : MarkovBanditPolicy k S)
    (hpi : IsGittinsIndexPolicy P r α pi)
    (h : MarkovBanditHistory k S n) (i : Fin k)
    (hi : ¬ ∀ j, gittinsIndex P r α (h.2 j) ≤
      gittinsIndex P r α (h.2 i)) :
    (pi.select n) h {i} = 0 := by
  let good : Set (Fin k) := {a | ∀ j,
    gittinsIndex P r α (h.2 j) ≤ gittinsIndex P r α (h.2 a)}
  have hgood : MeasurableSet good := Set.toFinite good |>.measurableSet
  have hcomp : (pi.select n) h goodᶜ = 0 := by
    rw [measure_compl hgood (measure_ne_top _ _)]
    rw [hpi n h]
    simp
  apply measure_mono_null (t := goodᶜ) _ hcomp
  intro z hz
  have hzi : z = i := by simpa using hz
  subst z
  simpa [good] using hi


theorem finite_greedy_of_markovBanditStackActionLikelihood_ne_zero
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (pi : MarkovBanditPolicy k S)
    (hpi : IsGittinsIndexPolicy P r α pi)
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k)
    (ha : markovBanditStackActionLikelihood pi a omega ≠ 0) :
    ∀ t : Fin n, ∀ j : Fin k,
      gittinsIndex P r α
          (omega j (finiteStackPullCountBefore a j t)) ≤
        gittinsIndex P r α
          (omega (a t) (finiteStackPullCountBefore a (a t) t)) := by
  intro t j
  have hfactor : (pi.select (t : ℕ))
      (markovBanditPrefixHistoryBefore a
        (markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n) omega) t.castSucc) {a t} ≠ 0 := by
    intro hz
    apply ha
    rw [markovBanditStackActionLikelihood,
      markovBanditActionLikelihood]
    apply Finset.prod_eq_zero (Finset.mem_univ t)
    exact hz
  by_contra hnot
  have hz := gittinsPolicy_select_singleton_eq_zero_of_not_max
    P r α pi hpi
      (markovBanditPrefixHistoryBefore a
        (markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n) omega) t.castSucc)
      (a t)
  apply hfactor
  apply hz
  push_neg
  refine ⟨j, ?_⟩
  simpa [markovBanditPrefixHistoryBefore] using (lt_of_not_ge hnot)


noncomputable def markovBanditFullHistoryRoundCharge
    {k n : ℕ} {S : Type*}
    (g : S → ℝ) (h : MarkovBanditHistory k S (n + 1)) : ℝ :=
  currentHistoryPrevailingCharge g n
    (truncateMarkovBanditHistory h) ((h.1 (Fin.last n)).2)

lemma measurable_markovBanditFullHistoryRoundCharge
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    {g : S → ℝ} (hg : Measurable g) :
    Measurable (markovBanditFullHistoryRoundCharge
      (k := k) (n := n) g) := by
  have hjoint : Measurable
      (fun q : MarkovBanditHistory k S n × Fin k ↦
        currentHistoryPrevailingCharge g n q.1 q.2) :=
    measurable_from_prod_countable_left fun i ↦ by
      simpa using measurable_currentHistoryPrevailingCharge hg n i
  exact hjoint.comp
    (measurable_truncateMarkovBanditHistory.prodMk
      (measurable_snd.comp
        ((measurable_pi_apply (Fin.last n)).comp measurable_fst)))

lemma integrable_markovBanditFullHistoryRoundCharge
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    Integrable (markovBanditFullHistoryRoundCharge
      (k := k) (n := n) (gittinsIndex P r α))
      (markovBanditMeasure P pi x (n + 1)) := by
  rw [markovBanditMeasure]
  apply (integrable_map_measure
    (measurable_markovBanditFullHistoryRoundCharge
      (measurable_gittinsIndex_of_discounted
        P hr hα0 hα1 hint)).aestronglyMeasurable
    measurable_markovBanditSnoc.aemeasurable).2
  have hs := integrable_selectedCurrentHistoryPrevailingCharge_step
    (n := n) P hr hα0 hα1 hint pi x
  convert hs using 1
  funext p
  simp [markovBanditFullHistoryRoundCharge,
    truncateMarkovBanditHistory_snoc, Fin.snoc]

def markovBanditFiniteActionExtend
    {k n : ℕ} (a : Fin (n + 1) → Fin k) : ℕ → Fin k :=
  fun t ↦ if ht : t < n + 1 then a ⟨t, ht⟩ else a 0

@[simp] lemma markovBanditFiniteActionExtend_apply
    {k n : ℕ} (a : Fin (n + 1) → Fin k) (t : Fin (n + 1)) :
    markovBanditFiniteActionExtend a t = a t := by
  simp [markovBanditFiniteActionExtend, t.isLt]

lemma markovBanditFiniteStackHistory_eq_stackHistory_extend
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S)
    (a : Fin (n + 1) → Fin k) :
    markovBanditFiniteStackHistory omega a =
      markovBanditStackHistory (n := n + 1) omega
        (markovBanditFiniteActionExtend a) := by
  have hae : (fun s : Fin (n + 1) ↦
      markovBanditFiniteActionExtend a s) = a := by
    funext s
    exact markovBanditFiniteActionExtend_apply a s
  apply Prod.ext
  · funext t
    apply Prod.ext
    · funext i
      change omega i (finiteStackPullCountBefore a i t) =
        omega i (stackPullCountBefore (markovBanditFiniteActionExtend a) i t)
      congr 1
      calc
        finiteStackPullCountBefore a i t =
            finiteStackPullCountBefore
              (fun s : Fin (n + 1) ↦ markovBanditFiniteActionExtend a s)
              i t := by rw [hae]
        _ = stackPullCountBefore (markovBanditFiniteActionExtend a) i t :=
          finiteStackPullCountBefore_restrict
            (markovBanditFiniteActionExtend a) i t
              (Nat.le_of_lt t.isLt)
    · change a t = markovBanditFiniteActionExtend a t
      exact (markovBanditFiniteActionExtend_apply a t).symm
  · funext i
    change omega i (finiteStackPullCountBefore a i (n + 1)) =
      omega i (stackPullCountBefore (markovBanditFiniteActionExtend a) i (n + 1))
    congr 1
    calc
      finiteStackPullCountBefore a i (n + 1) =
          finiteStackPullCountBefore
            (fun s : Fin (n + 1) ↦ markovBanditFiniteActionExtend a s)
            i (n + 1) := by rw [hae]
      _ = stackPullCountBefore (markovBanditFiniteActionExtend a) i (n + 1) :=
        finiteStackPullCountBefore_restrict
          (markovBanditFiniteActionExtend a) i (n + 1) le_rfl

noncomputable def finiteChargeStackInterleaving
    {k n : ℕ} (H : Fin k → ℕ → ℝ)
    (a : Fin (n + 1) → Fin k) : ℝ :=
  H (a (Fin.last n))
    (finiteStackPullCountBefore a (a (Fin.last n)) n)

lemma markovBanditFullHistoryRoundCharge_finiteStackHistory
    {k n : ℕ} {S : Type*} (g : S → ℝ)
    (omega : MarkovBanditStackSpace k S)
    (a : Fin (n + 1) → Fin k) :
    markovBanditFullHistoryRoundCharge g
        (markovBanditFiniteStackHistory omega a) =
      finiteChargeStackInterleaving
        (markovBanditArmPrevailingChargeStack g omega) a := by
  let ae := markovBanditFiniteActionExtend a
  rw [markovBanditFiniteStackHistory_eq_stackHistory_extend]
  rw [markovBanditFullHistoryRoundCharge]
  rw [truncate_markovBanditStackHistory]
  change currentHistoryPrevailingCharge g n
      (markovBanditStackHistory (n := n) omega ae) (ae n) = _
  rw [selectedCurrentHistoryPrevailingCharge_markovBanditStackHistory]
  change markovBanditArmPrevailingChargeStack g omega (ae n)
      (stackPullCountBefore ae (ae n) n) = _
  have haen : ae n = a (Fin.last n) := by
    simpa [ae] using
      (markovBanditFiniteActionExtend_apply a (Fin.last n))
  rw [haen]
  change markovBanditArmPrevailingChargeStack g omega (a (Fin.last n))
      (stackPullCountBefore ae (a (Fin.last n)) n) =
    markovBanditArmPrevailingChargeStack g omega (a (Fin.last n))
      (finiteStackPullCountBefore a (a (Fin.last n)) n)
  congr 1
  have hae : (fun s : Fin (n + 1) ↦ ae s) = a := by
    funext s
    exact markovBanditFiniteActionExtend_apply a s
  calc
    stackPullCountBefore ae (a (Fin.last n)) n =
        finiteStackPullCountBefore (fun s : Fin (n + 1) ↦ ae s)
          (a (Fin.last n)) n :=
      (finiteStackPullCountBefore_restrict ae
        (a (Fin.last n)) n (Nat.le_succ n)).symm
    _ = finiteStackPullCountBefore a (a (Fin.last n)) n := by rw [hae]

lemma withDensity_stackActionLikelihood_snoc_le
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) (i : Fin k) :
    (markovBanditStackMeasure P x).withDensity
        (markovBanditStackActionLikelihood pi (Fin.snoc a i)) ≤
      (markovBanditStackMeasure P x).withDensity
        (markovBanditStackActionLikelihood pi a) := by
  rw [← sum_withDensity_stackActionLikelihood_snoc P pi x a]
  rw [← Measure.sum_fintype]
  exact Measure.le_sum
    (fun j : Fin k ↦ (markovBanditStackMeasure P x).withDensity
      (markovBanditStackActionLikelihood pi (Fin.snoc a j))) i

lemma integrable_finiteChargeStackInterleaving_withDensity
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin (n + 1) → Fin k) :
    Integrable
      (fun omega ↦ finiteChargeStackInterleaving
        (markovBanditArmPrevailingChargeStack
          (gittinsIndex P r α) omega) a)
      ((markovBanditStackMeasure P x).withDensity
        (markovBanditStackActionLikelihood pi a)) := by
  have hfull := integrable_markovBanditFullHistoryRoundCharge
    (n := n) P hr hα0 hα1 hint pi x
  rw [markovBanditMeasure_eq_sum_fixedActionHistoryMeasure] at hfull
  rw [← Measure.sum_fintype] at hfull
  have ha := hfull.mono_measure
    (Measure.le_sum
      (fun b : Fin (n + 1) → Fin k ↦
        markovBanditFixedActionHistoryMeasure P pi x b) a)
  rw [markovBanditFixedActionHistoryMeasure] at ha
  have hm : Measurable (fun omega : MarkovBanditStackSpace k S ↦
      markovBanditFiniteStackHistory omega a) :=
    measurable_markovBanditFiniteStackHistory.comp
      (measurable_id.prodMk measurable_const)
  have hs := (integrable_map_measure
    (measurable_markovBanditFullHistoryRoundCharge
      (measurable_gittinsIndex_of_discounted
        P hr hα0 hα1 hint)).aestronglyMeasurable
    hm.aemeasurable).1 ha
  apply hs.congr
  exact Filter.Eventually.of_forall fun omega ↦ by
    exact markovBanditFullHistoryRoundCharge_finiteStackHistory
      (gittinsIndex P r α) omega a

noncomputable def finiteDiscountedChargeStackInterleaving
    {k n : ℕ} (α : ℝ) (H : Fin k → ℕ → ℝ)
    (a : Fin n → Fin k) : ℝ :=
  ∑ t : Fin n, α ^ (t : ℕ) *
    H (a t) (finiteStackPullCountBefore a (a t) t)

lemma finiteDiscountedChargeStackInterleaving_snoc
    {k n : ℕ} (α : ℝ) (H : Fin k → ℕ → ℝ)
    (a : Fin n → Fin k) (i : Fin k) :
    finiteDiscountedChargeStackInterleaving α H (Fin.snoc a i) =
      finiteDiscountedChargeStackInterleaving α H a +
        α ^ n * finiteChargeStackInterleaving H (Fin.snoc a i) := by
  rw [finiteDiscountedChargeStackInterleaving,
    finiteDiscountedChargeStackInterleaving]
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [Fin.snoc_castSucc]
    change α ^ (t : ℕ) *
        H (a t) (finiteStackPullCountBefore (Fin.snoc a i) (a t) t) =
      α ^ (t : ℕ) * H (a t) (finiteStackPullCountBefore a (a t) t)
    rw [finiteStackPullCountBefore_snoc_before a (a t) i t
      (Nat.le_of_lt t.isLt)]

theorem integrable_finiteDiscountedChargeStackInterleaving_withDensity
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ {n : ℕ} (a : Fin n → Fin k),
      Integrable
        (fun omega ↦ finiteDiscountedChargeStackInterleaving α
          (markovBanditArmPrevailingChargeStack
            (gittinsIndex P r α) omega) a)
        ((markovBanditStackMeasure P x).withDensity
          (markovBanditStackActionLikelihood pi a)) := by
  intro n
  induction n with
  | zero =>
      intro a
      simpa [finiteDiscountedChargeStackInterleaving] using
        (integrable_zero _ : Integrable
          (fun _ : MarkovBanditStackSpace k S ↦ (0 : ℝ))
          ((markovBanditStackMeasure P x).withDensity
            (markovBanditStackActionLikelihood pi a)))
  | succ n ih =>
      intro b
      let a := markovBanditActionPrefix b
      let i := markovBanditLastAction b
      have hb : b = Fin.snoc a i := by
        change b = Fin.snoc (Fin.init b) (b (Fin.last n))
        exact (Fin.snoc_init_self b).symm
      have hold := (ih a).mono_measure
        (withDensity_stackActionLikelihood_snoc_le P pi x a i)
      have hlast :=
        (integrable_finiteChargeStackInterleaving_withDensity
          P hr hα0 hα1 hint pi x (Fin.snoc a i)).const_mul (α ^ n)
      rw [hb]
      apply (hold.add hlast).congr
      exact Filter.Eventually.of_forall fun omega ↦ by
        exact (finiteDiscountedChargeStackInterleaving_snoc α
          (markovBanditArmPrevailingChargeStack
            (gittinsIndex P r α) omega) a i).symm

noncomputable def markovBanditFiniteStackChargeValue
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) (N : ℕ) : ℝ :=
  ∑ a : Fin N → Fin k,
    ∫ omega, finiteDiscountedChargeStackInterleaving α
        (markovBanditArmPrevailingChargeStack
          (gittinsIndex P r α) omega) a
      ∂(markovBanditStackMeasure P x).withDensity
        (markovBanditStackActionLikelihood pi a)

def IsGreedyChargeStackInterleavingBefore {k : ℕ}
    (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k) (N : ℕ) : Prop :=
  ∀ n, n < N → ∀ i,
    H i (stackPullCountBefore a i n) ≤
      H (a n) (stackPullCountBefore a (a n) n)

theorem isGreedyChargeStackInterleavingBefore_of_likelihood_ne_zero
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (pi : MarkovBanditPolicy k S)
    (hpi : IsGittinsIndexPolicy P r α pi)
    (omega : MarkovBanditStackSpace k S)
    (a : Fin (n + 1) → Fin k)
    (ha : markovBanditStackActionLikelihood pi a omega ≠ 0) :
    IsGreedyChargeStackInterleavingBefore
      (markovBanditArmPrevailingChargeStack
        (gittinsIndex P r α) omega)
      (markovBanditFiniteActionExtend a) (n + 1) := by
  let ae := markovBanditFiniteActionExtend a
  have hfin := finite_greedy_of_markovBanditStackActionLikelihood_ne_zero
    P r α pi hpi omega a ha
  intro t ht i
  let tf : Fin (n + 1) := ⟨t, ht⟩
  let h : MarkovBanditHistory k S t :=
    markovBanditStackHistory (n := t) omega ae
  have hstate : HasBanditStateUpdates h :=
    hasBanditStateUpdates_markovBanditStackHistory omega ae
  have hgreedy : IsGreedyIndexHistory (gittinsIndex P r α) h := by
    intro q j
    let qf : Fin (n + 1) := ⟨q, lt_trans q.isLt ht⟩
    have hq := hfin qf j
    have hae : (fun s : Fin (n + 1) ↦ ae s) = a := by
      funext s
      exact markovBanditFiniteActionExtend_apply a s
    have hcj : finiteStackPullCountBefore a j q =
        stackPullCountBefore ae j q := by
      calc
        finiteStackPullCountBefore a j q =
            finiteStackPullCountBefore (fun s : Fin (n + 1) ↦ ae s) j q := by
          rw [hae]
        _ = stackPullCountBefore ae j q :=
          finiteStackPullCountBefore_restrict ae j q
            (Nat.le_of_lt (lt_trans q.isLt ht))
    have haq : ae q = a qf := by
      simpa [qf] using (markovBanditFiniteActionExtend_apply a qf)
    have hca : finiteStackPullCountBefore a (a qf) q =
        stackPullCountBefore ae (ae q) q := by
      rw [haq]
      calc
        finiteStackPullCountBefore a (a qf) q =
            finiteStackPullCountBefore (fun s : Fin (n + 1) ↦ ae s)
              (a qf) q := by rw [hae]
        _ = stackPullCountBefore ae (a qf) q :=
          finiteStackPullCountBefore_restrict ae _ q
            (Nat.le_of_lt (lt_trans q.isLt ht))
    change gittinsIndex P r α (omega j (stackPullCountBefore ae j q)) ≤
      gittinsIndex P r α (omega (ae q) (stackPullCountBefore ae (ae q) q))
    have hca' : finiteStackPullCountBefore a (a qf) q =
        stackPullCountBefore ae (a qf) q := by simpa [haq] using hca
    rw [haq, ← hcj, ← hca']
    exact hq
  have hchoice : ∀ j : Fin k,
      gittinsIndex P r α (h.2 j) ≤
        gittinsIndex P r α (h.2 (ae t)) := by
    intro j
    have htmax := hfin tf j
    change gittinsIndex P r α
        (omega j (finiteStackPullCountBefore a j t)) ≤
      gittinsIndex P r α
        (omega (a tf) (finiteStackPullCountBefore a (a tf) t)) at htmax
    have hae : (fun s : Fin (n + 1) ↦ ae s) = a := by
      funext s
      exact markovBanditFiniteActionExtend_apply a s
    have hcj : finiteStackPullCountBefore a j t =
        stackPullCountBefore ae j t := by
      calc
        finiteStackPullCountBefore a j t =
            finiteStackPullCountBefore (fun s : Fin (n + 1) ↦ ae s) j t := by
          rw [hae]
        _ = stackPullCountBefore ae j t :=
          finiteStackPullCountBefore_restrict ae j t (Nat.le_of_lt ht)
    have hat : ae t = a tf := markovBanditFiniteActionExtend_apply a tf
    have hca : finiteStackPullCountBefore a (a tf) t =
        stackPullCountBefore ae (ae t) t := by
      rw [hat]
      calc
        finiteStackPullCountBefore a (a tf) t =
            finiteStackPullCountBefore (fun s : Fin (n + 1) ↦ ae s)
              (a tf) t := by rw [hae]
        _ = stackPullCountBefore ae (a tf) t :=
          finiteStackPullCountBefore_restrict ae _ t (Nat.le_of_lt ht)
    change gittinsIndex P r α (omega j (stackPullCountBefore ae j t)) ≤
      gittinsIndex P r α (omega (ae t) (stackPullCountBefore ae (ae t) t))
    have hca' : finiteStackPullCountBefore a (a tf) t =
        stackPullCountBefore ae (a tf) t := by simpa [hat] using hca
    rw [hat, ← hcj, ← hca']
    exact htmax
  have hmax := (currentHistoryPrevailingCharge_invariant
    (gittinsIndex P r α) h hstate hgreedy (ae t) hchoice).1 i
  simpa [h, chargeStackInterleaving,
    currentHistoryPrevailingCharge_markovBanditStackHistory] using hmax

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



lemma markovBanditStackActionLikelihood_le_one
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) :
    markovBanditStackActionLikelihood pi a omega ≤ 1 := by
  have hsingle : markovBanditStackActionLikelihood pi a omega ≤
      ∑ b : Fin n → Fin k,
        markovBanditStackActionLikelihood pi b omega :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun b : Fin n → Fin k ↦
        markovBanditStackActionLikelihood pi b omega)
      (fun _ _ ↦ bot_le) (Finset.mem_univ a)
  simpa [sum_markovBanditStackActionLikelihood pi omega n] using hsingle

lemma markovBanditStackActionLikelihood_lt_top
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) :
    markovBanditStackActionLikelihood pi a omega < ⊤ :=
  lt_of_le_of_lt (markovBanditStackActionLikelihood_le_one pi omega a)
    ENNReal.one_lt_top

lemma sum_markovBanditStackActionLikelihood_toReal
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S) :
    ∑ a : Fin n → Fin k,
        (markovBanditStackActionLikelihood pi a omega).toReal = 1 := by
  rw [← ENNReal.toReal_sum]
  · rw [sum_markovBanditStackActionLikelihood]
    simp
  · intro a ha
    exact ne_of_lt (markovBanditStackActionLikelihood_lt_top pi omega a)

theorem finiteDiscountedChargeStackInterleaving_average_le_gittins
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (pi piStar : MarkovBanditPolicy k S)
    (hpiStar : IsGittinsIndexPolicy P r α piStar)
    (omega : MarkovBanditStackSpace k S) :
    (∑ a : Fin N → Fin k,
        (markovBanditStackActionLikelihood pi a omega).toReal *
          finiteDiscountedChargeStackInterleaving α
            (markovBanditArmPrevailingChargeStack
              (gittinsIndex P r α) omega) a) ≤
      ∑ b : Fin N → Fin k,
        (markovBanditStackActionLikelihood piStar b omega).toReal *
          finiteDiscountedChargeStackInterleaving α
            (markovBanditArmPrevailingChargeStack
              (gittinsIndex P r α) omega) b := by
  by_cases hN : N = 0
  · subst N
    simp [finiteDiscountedChargeStackInterleaving]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  let H := markovBanditArmPrevailingChargeStack
    (gittinsIndex P r α) omega
  let L := fun (rho : MarkovBanditPolicy k S) (a : Fin (n + 1) → Fin k) ↦
    (markovBanditStackActionLikelihood rho a omega).toReal
  let V := fun (a : Fin (n + 1) → Fin k) ↦
    finiteDiscountedChargeStackInterleaving α H a
  have hsumL : ∀ rho : MarkovBanditPolicy k S,
      ∑ a : Fin (n + 1) → Fin k, L rho a = 1 := by
    intro rho
    exact sum_markovBanditStackActionLikelihood_toReal rho omega
  have hpair : ∀ (a b : Fin (n + 1) → Fin k),
      L pi a * L piStar b * V a ≤
        L pi a * L piStar b * V b := by
    intro a b
    by_cases hb : markovBanditStackActionLikelihood piStar b omega = 0
    · simp [L, hb]
    · have hgreedy :=
        isGreedyChargeStackInterleavingBefore_of_likelihood_ne_zero
          P r α piStar hpiStar omega (a := b) hb
      have hle : V a ≤ V b := by
        let ae := markovBanditFiniteActionExtend a
        let be := markovBanditFiniteActionExtend b
        have hfinite := discounted_sum_chargeStackInterleaving_le_greedy_before
          (fun i ↦ antitone_markovBanditArmPrevailingChargeStack
            (gittinsIndex P r α) omega i)
          hgreedy hα0 hα1 ae
        have hVextend : ∀ c : Fin (n + 1) → Fin k,
            V c = ∑ t ∈ Finset.range (n + 1), α ^ t *
              chargeStackInterleaving H
                (markovBanditFiniteActionExtend c) t := by
          intro c
          change finiteDiscountedChargeStackInterleaving α H c = _
          rw [finiteDiscountedChargeStackInterleaving]
          calc
            (∑ t : Fin (n + 1), α ^ (t : ℕ) *
                H (c t) (finiteStackPullCountBefore c (c t) t)) =
                ∑ t : Fin (n + 1), α ^ (t : ℕ) *
                  chargeStackInterleaving H
                    (markovBanditFiniteActionExtend c) t := by
              apply Finset.sum_congr rfl
              intro t ht
              have ht' : (t : ℕ) ≤ n + 1 := Nat.le_of_lt t.isLt
              change α ^ (t : ℕ) * H (c t)
                  (finiteStackPullCountBefore c (c t) t) = _
              rw [chargeStackInterleaving]
              rw [show markovBanditFiniteActionExtend c t = c t by
                exact markovBanditFiniteActionExtend_apply c t]
              have hr := finiteStackPullCountBefore_restrict
                (n := n + 1) (markovBanditFiniteActionExtend c) (c t) t ht'
              have hc : (fun s : Fin (n + 1) ↦
                  markovBanditFiniteActionExtend c s) = c := by
                funext s
                exact markovBanditFiniteActionExtend_apply c s
              have hcount : finiteStackPullCountBefore c (c t) t =
                  stackPullCountBefore
                    (markovBanditFiniteActionExtend c) (c t) t :=
                (congrArg (fun d : Fin (n + 1) → Fin k ↦
                  finiteStackPullCountBefore d (c t) t) hc.symm).trans hr
              exact congrArg (fun q ↦ α ^ (t : ℕ) * H (c t) q) hcount
            _ = _ := Fin.sum_univ_eq_sum_range
              (fun t ↦ α ^ t * chargeStackInterleaving H
                (markovBanditFiniteActionExtend c) t) (n + 1)
        rw [hVextend a, hVextend b]
        exact hfinite
      exact mul_le_mul_of_nonneg_left hle
        (mul_nonneg (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg))
  calc
    (∑ a : Fin (n + 1) → Fin k, L pi a * V a) =
        ∑ a : Fin (n + 1) → Fin k, ∑ b : Fin (n + 1) → Fin k,
          L pi a * L piStar b * V a := by
      apply Finset.sum_congr rfl
      intro a ha
      calc
        L pi a * V a = L pi a * (1 * V a) := by ring
        _ = L pi a * ((∑ b : Fin (n + 1) → Fin k,
            L piStar b) * V a) := by rw [hsumL piStar]
        _ = ∑ b : Fin (n + 1) → Fin k,
            L pi a * L piStar b * V a := by
          rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    _ ≤ ∑ a : Fin (n + 1) → Fin k, ∑ b : Fin (n + 1) → Fin k,
          L pi a * L piStar b * V b := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      exact hpair a b
    _ = ∑ b : Fin (n + 1) → Fin k, L piStar b * V b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      calc
        (∑ a : Fin (n + 1) → Fin k,
            L pi a * L piStar b * V b) =
            (∑ a : Fin (n + 1) → Fin k, L pi a) *
              (L piStar b * V b) := by
          rw [Finset.sum_mul]
          simp only [mul_assoc]
        _ = L piStar b * V b := by rw [hsumL pi]; ring

theorem markovBanditFiniteStackChargeValue_eq_integral_average
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditFiniteStackChargeValue P r α pi x N =
      ∫ omega, ∑ a : Fin N → Fin k,
        (markovBanditStackActionLikelihood pi a omega).toReal *
          finiteDiscountedChargeStackInterleaving α
            (markovBanditArmPrevailingChargeStack
              (gittinsIndex P r α) omega) a
        ∂markovBanditStackMeasure P x := by
  let M := markovBanditStackMeasure P x
  let L := fun (a : Fin N → Fin k) ↦
    markovBanditStackActionLikelihood pi a
  let V := fun (a : Fin N → Fin k) (omega : MarkovBanditStackSpace k S) ↦
    finiteDiscountedChargeStackInterleaving α
      (markovBanditArmPrevailingChargeStack
        (gittinsIndex P r α) omega) a
  have hL : ∀ a : Fin N → Fin k, Measurable (L a) :=
    fun a ↦ measurable_markovBanditStackActionLikelihood pi a
  have hLtop : ∀ a : Fin N → Fin k, ∀ᵐ omega ∂M, L a omega < ⊤ :=
    fun a ↦ Filter.Eventually.of_forall fun omega ↦
      markovBanditStackActionLikelihood_lt_top pi omega a
  have hV : ∀ a : Fin N → Fin k,
      Integrable (V a) (M.withDensity (L a)) := by
    intro a
    exact integrable_finiteDiscountedChargeStackInterleaving_withDensity
      P hr hα0 hα1 hint pi x a
  have hweighted : ∀ a : Fin N → Fin k,
      Integrable (fun omega ↦ (L a omega).toReal * V a omega) M := by
    intro a
    simpa only [mul_comm] using
      (integrable_withDensity_iff (hL a) (hLtop a)).1 (hV a)
  rw [markovBanditFiniteStackChargeValue]
  calc
    (∑ a : Fin N → Fin k, ∫ omega, V a omega ∂M.withDensity (L a)) =
        ∑ a : Fin N → Fin k,
          ∫ omega, (L a omega).toReal * V a omega ∂M := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_withDensity_eq_integral_toReal_smul
        (hL a) (hLtop a)]
      simp only [smul_eq_mul]
    _ = ∫ omega, ∑ a : Fin N → Fin k,
          (L a omega).toReal * V a omega ∂M := by
      rw [integral_finset_sum]
      exact fun a _ ↦ hweighted a

theorem markovBanditFiniteStackChargeValue_le_gittins
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (pi piStar : MarkovBanditPolicy k S)
    (hpiStar : IsGittinsIndexPolicy P r α piStar)
    (x : Fin k → S) :
    markovBanditFiniteStackChargeValue P r α pi x N ≤
      markovBanditFiniteStackChargeValue P r α piStar x N := by
  rw [markovBanditFiniteStackChargeValue_eq_integral_average
    P hr hα0 hα1 hint pi x]
  rw [markovBanditFiniteStackChargeValue_eq_integral_average
    P hr hα0 hα1 hint piStar x]
  let M := markovBanditStackMeasure P x
  let F := fun (rho : MarkovBanditPolicy k S)
      (omega : MarkovBanditStackSpace k S) ↦
    ∑ a : Fin N → Fin k,
      (markovBanditStackActionLikelihood rho a omega).toReal *
        finiteDiscountedChargeStackInterleaving α
          (markovBanditArmPrevailingChargeStack
            (gittinsIndex P r α) omega) a
  have hFint : ∀ rho : MarkovBanditPolicy k S, Integrable (F rho) M := by
    intro rho
    apply MeasureTheory.integrable_finsetSum
    intro a ha
    let L := markovBanditStackActionLikelihood rho a
    let V := fun omega : MarkovBanditStackSpace k S ↦
      finiteDiscountedChargeStackInterleaving α
        (markovBanditArmPrevailingChargeStack
          (gittinsIndex P r α) omega) a
    have hV : Integrable V (M.withDensity L) :=
      integrable_finiteDiscountedChargeStackInterleaving_withDensity
        P hr hα0 hα1 hint rho x a
    simpa only [mul_comm] using
      (integrable_withDensity_iff
        (measurable_markovBanditStackActionLikelihood rho a)
        (Filter.Eventually.of_forall fun omega ↦
          markovBanditStackActionLikelihood_lt_top rho omega a)).1 hV
  apply integral_mono (hFint pi) (hFint piStar)
  intro omega
  exact finiteDiscountedChargeStackInterleaving_average_le_gittins
    P r hα0.le hα1.le pi piStar hpiStar omega



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal


theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (π πstar : BanditAlgorithm.MarkovBanditPolicy k S)
    (hπstar : BanditAlgorithm.IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (N : ℕ) :
    let stackValue := fun (ρ : BanditAlgorithm.MarkovBanditPolicy k S) ↦
      let count := fun (a : Fin N → Fin k) (i : Fin k) (t : ℕ) ↦
        ∑ s : Fin N, if (s : ℕ) < t ∧ a s = i then 1 else 0
      let historyBefore := fun (a : Fin N → Fin k)
          (ω : Fin k → ℕ → S) (t : Fin N) ↦
        ((fun u : Fin (t : ℕ) ↦
            ((fun i ↦ ω i (count a i u)),
              a ⟨u, lt_trans u.isLt t.isLt⟩)),
          fun i ↦ ω i (count a i t))
      let likelihood := fun (a : Fin N → Fin k) (ω : Fin k → ℕ → S) ↦
        ∏ t : Fin N, (ρ.select t) (historyBefore a ω t) {a t}
      let charge := fun (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) ↦
        (Finset.range (u + 1)).inf'
          ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
          (fun v ↦ BanditAlgorithm.gittinsIndex P r α (ω i v))
      let value := fun (a : Fin N → Fin k) (ω : Fin k → ℕ → S) ↦
        ∑ t : Fin N, α ^ (t : ℕ) *
          charge ω (a t) (count a (a t) t)
      let stackMeasure : Measure (Fin k → ℕ → S) :=
        Measure.pi (fun i ↦ BanditAlgorithm.markovChainMeasure P (x i))
      ∑ a : Fin N → Fin k,
        ∫ ω, value a ω ∂stackMeasure.withDensity (likelihood a)
    stackValue π ≤ stackValue πstar := by
  change BanditAlgorithm.markovBanditFiniteStackChargeValue P r α π x N ≤
    BanditAlgorithm.markovBanditFiniteStackChargeValue P r α πstar x N
  exact BanditAlgorithm.markovBanditFiniteStackChargeValue_le_gittins
    P hr hα0 hα1 hint π πstar hπstar x
