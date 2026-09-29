-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_action_realisation_ae
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-03T01:23:18.231005+00:00
-- url     : https://prove2.me/submissions/29c8c242-2bc3-45fc-b5eb-28453f386f67

import Definitions.Def_UCRL2Algorithm
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

open MeasureTheory ProbabilityTheory Finset BanditAlgorithm
open scoped NNReal ENNReal

namespace ActRealise

variable {S A : ℕ}

/-! ### Reading a `Fin.snoc` trajectory -/

lemma snoc_apply_lt {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A)
    (i : Fin (m + 1)) (hi : i.val < m) :
    (Fin.snoc h p : MDPTrajectory S A (m + 1)) i = h ⟨i.val, hi⟩ := by
  simp only [Fin.snoc, hi, dif_pos]
  rfl

lemma snoc_apply_last {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A) :
    (Fin.snoc h p : MDPTrajectory S A (m + 1)) (Fin.last m) = p := by
  simp

lemma succ_snoc_castSucc {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A)
    (j : Fin m) (hj : j.val + 1 < m) :
    mdpSuccessor (Fin.snoc h p) (Fin.castSucc j) = mdpSuccessor h j := by
  simp only [mdpSuccessor, Fin.val_castSucc]
  rw [dif_pos (show j.val + 1 < m + 1 by omega), dif_pos hj]
  have hidx : (⟨j.val + 1, show j.val + 1 < m + 1 by omega⟩ : Fin (m + 1))
      = Fin.castSucc ⟨j.val + 1, hj⟩ := Fin.ext rfl
  rw [hidx, Fin.snoc_castSucc]

/-! ### Counts are determined by the prefix -/

lemma visitCount_snoc {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A) {k : ℕ}
    (hk : k ≤ m) (s : Fin S) (a : Fin A) :
    mdpVisitCount (Fin.snoc h p) k s a = mdpVisitCount h k s a := by
  classical
  have hk' : ¬ (m < k) := by omega
  simp only [mdpVisitCount, Finset.card_filter, Fin.sum_univ_castSucc, Fin.val_castSucc,
    Fin.snoc_castSucc, Fin.val_last, hk', false_and, if_false, add_zero]

lemma transitionCount_snoc {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A) {k : ℕ}
    (hk : k ≤ m) (s : Fin S) (a : Fin A) (s' : Fin S) :
    mdpTransitionCount (Fin.snoc h p) k s a s' = mdpTransitionCount h k s a s' := by
  classical
  have hk' : ¬ (m + 1 < k) := by omega
  simp only [mdpTransitionCount, Finset.card_filter, Fin.sum_univ_castSucc, Fin.val_castSucc,
    Fin.snoc_castSucc, Fin.val_last, hk', false_and, if_false, add_zero]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hjk : j.val + 1 < k
  · rw [succ_snoc_castSucc h p j (by omega)]
  · simp [hjk]

lemma confidenceSet_snoc {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A) {k : ℕ}
    (hk : k ≤ m) (N : ℕ) (δ : ℝ) (s : Fin S) (a : Fin A) :
    mdpConfidenceSet (Fin.snoc h p) k N δ s a = mdpConfidenceSet h k N δ s a := by
  have hobs : mdpObservedCount (Fin.snoc h p) k s a = mdpObservedCount h k s a := by
    simp only [mdpObservedCount]
    exact Finset.sum_congr rfl fun s' _ ↦ transitionCount_snoc h p hk s a s'
  have hrow : mdpEmpiricalRow (Fin.snoc h p) k s a = mdpEmpiricalRow h k s a := by
    simp only [mdpEmpiricalRow, hobs, transitionCount_snoc h p hk s a]
  simp only [mdpConfidenceSet, hobs, hrow]

/-! ### The confidence sets do not see the current action -/

lemma transitionCount_snoc_action {m : ℕ} (h : MDPTrajectory S A m) (s : Fin S) (a b : Fin A)
    {k : ℕ} (hk : k ≤ m + 1) (x : Fin S) (y : Fin A) (x' : Fin S) :
    mdpTransitionCount (Fin.snoc h (s, a)) k x y x'
      = mdpTransitionCount (Fin.snoc h (s, b)) k x y x' := by
  classical
  simp only [mdpTransitionCount]
  congr 1
  refine Finset.filter_congr fun i _ ↦ ?_
  by_cases hi : i.val + 1 < k
  · have him : i.val < m := by omega
    have hsucc : ∀ c : Fin A, mdpSuccessor (Fin.snoc h (s, c)) i
        = some ((Fin.snoc h (s, c) : MDPTrajectory S A (m + 1)) ⟨i.val + 1, by omega⟩).1 := by
      intro c; simp only [mdpSuccessor, dif_pos (show i.val + 1 < m + 1 by omega)]
    have hentry : ∀ c : Fin A, (Fin.snoc h (s, c) : MDPTrajectory S A (m + 1)) i = h ⟨i.val, him⟩ :=
      fun c ↦ snoc_apply_lt h (s, c) i him
    have hnext : ∀ c : Fin A,
        ((Fin.snoc h (s, c) : MDPTrajectory S A (m + 1)) ⟨i.val + 1, by omega⟩).1
          = ((Fin.snoc h (s, a) : MDPTrajectory S A (m + 1)) ⟨i.val + 1, by omega⟩).1 := by
      intro c
      rcases Nat.lt_or_ge (i.val + 1) m with hlt | hge
      · rw [snoc_apply_lt h (s, c) _ hlt, snoc_apply_lt h (s, a) _ hlt]
      · have hlast : (⟨i.val + 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp; omega)
        rw [hlast, snoc_apply_last, snoc_apply_last]
    simp only [hsucc, hentry, hnext]
  · simp only [hi, false_and]

lemma confidenceSet_snoc_action {m : ℕ} (h : MDPTrajectory S A m) (s : Fin S) (a b : Fin A)
    {k : ℕ} (hk : k ≤ m + 1) (N : ℕ) (δ : ℝ) (x : Fin S) (y : Fin A) :
    mdpConfidenceSet (Fin.snoc h (s, a)) k N δ x y
      = mdpConfidenceSet (Fin.snoc h (s, b)) k N δ x y := by
  have hobs : mdpObservedCount (Fin.snoc h (s, a)) k x y
      = mdpObservedCount (Fin.snoc h (s, b)) k x y := by
    simp only [mdpObservedCount]
    exact Finset.sum_congr rfl fun s' _ ↦ transitionCount_snoc_action h s a b hk x y s'
  have hrow : mdpEmpiricalRow (Fin.snoc h (s, a)) k x y = mdpEmpiricalRow (Fin.snoc h (s, b)) k x y := by
    simp only [mdpEmpiricalRow, hobs, transitionCount_snoc_action h s a b hk x y]
  simp only [mdpConfidenceSet, hobs, hrow]

/-! ### The phase-start function is determined by the prefix -/

lemma phaseStart_succ' {m : ℕ} (h : MDPTrajectory S A m) (u : ℕ) :
    mdpPhaseStart h (u + 1) =
      if ∃ s a, max 1 (mdpVisitCount h (mdpPhaseStart h u) s a) ≤
          mdpVisitCount h (u + 1) s a - mdpVisitCount h (mdpPhaseStart h u) s a then
        u + 1
      else mdpPhaseStart h u := rfl

lemma phaseStart_le' {m : ℕ} (h : MDPTrajectory S A m) (u : ℕ) : mdpPhaseStart h u ≤ u := by
  induction u with
  | zero => exact le_of_eq rfl
  | succ u ih =>
      rw [phaseStart_succ']
      split
      · exact le_rfl
      · exact ih.trans (Nat.le_succ u)

lemma phaseStart_snoc {m : ℕ} (h : MDPTrajectory S A m) (p : Fin S × Fin A) {u : ℕ}
    (hu : u ≤ m) : mdpPhaseStart (Fin.snoc h p) u = mdpPhaseStart h u := by
  induction u with
  | zero => rfl
  | succ u ih =>
      have hu' : u ≤ m := by omega
      have ihu := ih hu'
      rw [phaseStart_succ', phaseStart_succ', ihu]
      have hle : mdpPhaseStart h u ≤ m := le_trans (phaseStart_le' h u) hu'
      simp only [visitCount_snoc h p hle, visitCount_snoc h p hu]

/-! ### The event that the policy's action was realised -/

/-- The set of trajectories of length `m` on which every action is the one prescribed by
the UCRL2 action map for the confidence sets read off the trajectory itself. -/
def Good [NeZero A] (n : ℕ) (δ : ℝ) (r : Fin S → Fin A → ℝ) (m : ℕ) : Set (MDPTrajectory S A m) :=
  {h | ∀ t : Fin m,
    (h t).2 = mdpOptimisticActionMap r
      (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t.val + 1) n δ x a) (h t).1}

lemma snoc_mem_Good {n : ℕ} {δ : ℝ} {r : Fin S → Fin A → ℝ} [NeZero A] {m : ℕ}
    {h : MDPTrajectory S A m} (hh : h ∈ Good n δ r m) (s : Fin S) :
    (Fin.snoc h (s, mdpOptimisticActionMap r (mdpUCRL2ConfidenceSets n δ h s) s)
      : MDPTrajectory S A (m + 1)) ∈ Good n δ r (m + 1) := by
  classical
  set a₀ := mdpOptimisticActionMap r (mdpUCRL2ConfidenceSets n δ h s) s with ha₀
  intro t
  rcases Nat.lt_or_ge t.val m with ht | ht
  · -- an old round: everything is read off the prefix
    have hτt : mdpPhaseStart h t.val ≤ t.val := phaseStart_le' h t.val
    have hτle : mdpPhaseStart h t.val ≤ m := le_trans hτt ht.le
    have hps : mdpPhaseStart (Fin.snoc h (s, a₀)) t.val = mdpPhaseStart h t.val :=
      phaseStart_snoc h (s, a₀) (le_of_lt ht)
    have hcs : ∀ x y, mdpConfidenceSet (Fin.snoc h (s, a₀))
        (mdpPhaseStart h t.val + 1) n δ x y
        = mdpConfidenceSet h (mdpPhaseStart h t.val + 1) n δ x y :=
      fun x y ↦ confidenceSet_snoc h (s, a₀) (by omega) n δ x y
    rw [snoc_apply_lt h (s, a₀) t ht, hps]
    simp only [hcs]
    exact hh ⟨t.val, ht⟩
  · -- the new round: the action is the one the policy chose
    have htlast : t = Fin.last m := Fin.ext (by simp; omega)
    subst htlast
    have hps : mdpPhaseStart (Fin.snoc h (s, a₀)) m = mdpPhaseStart h m :=
      phaseStart_snoc h (s, a₀) le_rfl
    have hcs : ∀ x y, mdpConfidenceSet (Fin.snoc h (s, a₀))
        (mdpPhaseStart h m + 1) n δ x y
        = mdpConfidenceSet (Fin.snoc h (s, (default : Fin A)))
            (mdpPhaseStart h m + 1) n δ x y := by
      intro x y
      exact confidenceSet_snoc_action h s a₀ default
        (by have := phaseStart_le' h m; omega) n δ x y
    rw [snoc_apply_last]
    simp only [Fin.val_last, hps, hcs]
    rw [ha₀]
    rfl

/-! ### The measure computation -/

lemma measure_Good (n : ℕ) (δ : ℝ) (r : Fin S → Fin A → ℝ) [NeZero A]
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (m : ℕ) :
    mdpMeasure M μ0 (ucrl2Policy n δ r) m (Good n δ r m) = 1 := by
  classical
  induction m with
  | zero =>
      have : Good n δ r 0 = (Set.univ : Set (MDPTrajectory S A 0)) := by
        ext h; simp [Good]
      rw [this]
      simp [mdpMeasure]
  | succ m ih =>
      have hstep : ∀ h' : MDPTrajectory S A m, h' ∈ Good n δ r m →
          (mdpStepKernel M μ0 (ucrl2Policy n δ r) m h')
            {p : Fin S × Fin A | (Fin.snoc h' p : MDPTrajectory S A (m + 1)) ∈ Good n δ r (m + 1)}
            = 1 := by
        intro h' hh'
        rw [mdpStepKernel, Kernel.compProd_apply MeasurableSet.of_discrete]
        have hinner : ∀ s : Fin S,
            ((ucrl2Policy n δ r).select m (h', s))
              (Prod.mk s ⁻¹' {p : Fin S × Fin A |
                (Fin.snoc h' p : MDPTrajectory S A (m + 1)) ∈ Good n δ r (m + 1)}) = 1 := by
          intro s
          rw [ucrl2Policy, Kernel.deterministic_apply, Measure.dirac_apply_of_mem]
          exact snoc_mem_Good hh' s
        simp only [hinner]
        rw [lintegral_one, measure_univ]
      have hmono : ∀ h' : MDPTrajectory S A m,
          Set.indicator (Good n δ r m) (fun _ ↦ (1 : ℝ≥0∞)) h'
            ≤ (mdpStepKernel M μ0 (ucrl2Policy n δ r) m h')
              {p : Fin S × Fin A |
                (Fin.snoc h' p : MDPTrajectory S A (m + 1)) ∈ Good n δ r (m + 1)} := by
        intro h'
        by_cases hg : h' ∈ Good n δ r m
        · rw [Set.indicator_of_mem hg, hstep h' hg]
        · simp [Set.indicator_of_notMem hg]
      have hkey : mdpMeasure M μ0 (ucrl2Policy n δ r) (m + 1) (Good n δ r (m + 1))
          = ∫⁻ h', (mdpStepKernel M μ0 (ucrl2Policy n δ r) m h')
              {p : Fin S × Fin A |
                (Fin.snoc h' p : MDPTrajectory S A (m + 1)) ∈ Good n δ r (m + 1)}
              ∂(mdpMeasure M μ0 (ucrl2Policy n δ r) m) := by
        rw [mdpMeasure, Measure.map_apply measurable_mdpTrajectorySnoc MeasurableSet.of_discrete,
          Measure.compProd_apply MeasurableSet.of_discrete]
        rfl
      refine le_antisymm ?_ ?_
      · rw [hkey]
        calc ∫⁻ h', (mdpStepKernel M μ0 (ucrl2Policy n δ r) m h')
                {p : Fin S × Fin A |
                  (Fin.snoc h' p : MDPTrajectory S A (m + 1)) ∈ Good n δ r (m + 1)}
                ∂(mdpMeasure M μ0 (ucrl2Policy n δ r) m)
            ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(mdpMeasure M μ0 (ucrl2Policy n δ r) m) := by
              refine lintegral_mono fun h' ↦ ?_
              exact prob_le_one
          _ = 1 := by simp
      · rw [hkey]
        calc (1 : ℝ≥0∞) = mdpMeasure M μ0 (ucrl2Policy n δ r) m (Good n δ r m) := ih.symm
          _ = ∫⁻ h', Set.indicator (Good n δ r m) (fun _ ↦ (1 : ℝ≥0∞)) h'
                ∂(mdpMeasure M μ0 (ucrl2Policy n δ r) m) := by
              rw [lintegral_indicator MeasurableSet.of_discrete]; simp
          _ ≤ _ := lintegral_mono (hmono)

end ActRealise

open ActRealise

theorem solution
    (S A n : ℕ) [NeZero A] (δ : ℝ) (r : Fin S → Fin A → ℝ)
    (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) :
    mdpMeasure M μ0 (ucrl2Policy n δ r) n
        {h : MDPTrajectory S A n | ∀ t : Fin n,
          (h t).2 = mdpOptimisticActionMap r
            (fun x a ↦ mdpConfidenceSet h (mdpPhaseStart h t.val + 1) n δ x a)
            (h t).1}ᶜ
      = 0 := by
  have hGood : mdpMeasure M μ0 (ucrl2Policy n δ r) n (Good n δ r n) = 1 :=
    measure_Good n δ r M μ0 n
  have hcompl := measure_compl (μ := mdpMeasure M μ0 (ucrl2Policy n δ r) n)
    (s := Good n δ r n) MeasurableSet.of_discrete (by rw [hGood]; exact ENNReal.one_ne_top)
  rw [hGood, measure_univ] at hcompl
  simpa using hcompl
