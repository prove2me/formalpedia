-- Prove2me | solution 1 for BanditAlgorithm.mdp_regret_lower_bound_jao_large_diameter
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T09:14:39.063719+00:00
-- url     : https://prove2.me/submissions/51d912c5-3a83-48f7-84e7-92da70d5d532

import Mathlib
import Definitions.Def_FiniteMDPLearning

open MeasureTheory ProbabilityTheory
open BanditAlgorithm


variable {S A : ℕ}

/-! ### Deterministic MDPs and their trajectory measures -/

/-- A deterministic MDP built from a transition function `next` and a reward `r`. -/
def jao_detMDP (next : Fin S → Fin A → Fin S) (r : Fin S → Fin A → ℝ)
    (hr : ∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) : FiniteMDP S A where
  P s a s' := if s' = next s a then 1 else 0
  P_sum_one s a := by simp
  r := r
  r_mem_Icc := hr

/-- The deterministic state sequence under a memoryless policy `f`. -/
def jao_pathState (next : Fin S → Fin A → Fin S) (f : Fin S → Fin A) (src : Fin S) :
    ℕ → Fin S
  | 0 => src
  | n + 1 => next (jao_pathState next f src n) (f (jao_pathState next f src n))

/-- The deterministic trajectory of `n` rounds. -/
def jao_path (next : Fin S → Fin A → Fin S) (f : Fin S → Fin A) (src : Fin S) (n : ℕ) :
    MDPTrajectory S A n :=
  fun t => (jao_pathState next f src t, f (jao_pathState next f src t))

lemma jao_pathState_add (next : Fin S → Fin A → Fin S) (f : Fin S → Fin A) (src : Fin S)
    (i j : ℕ) :
    jao_pathState next f src (i + j) = jao_pathState next f (jao_pathState next f src i) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [← Nat.add_assoc, jao_pathState, ih, jao_pathState]

lemma jao_stateDirac_toMeasure (src : Fin S) :
    (mdpStateDirac src).toMeasure = Measure.dirac src := by
  simp [MDPStateDistribution.toMeasure, mdpStateDirac]

lemma jao_transitionDist_det (next : Fin S → Fin A → Fin S) (r) (hr) (s : Fin S) (a : Fin A) :
    ((jao_detMDP next r hr).transitionDist s a).toMeasure = Measure.dirac (next s a) := by
  simp [MDPStateDistribution.toMeasure, FiniteMDP.transitionDist, jao_detMDP]

lemma jao_transitionKernel_det (next : Fin S → Fin A → Fin S) (r) (hr) (p : Fin S × Fin A) :
    mdpTransitionKernel (jao_detMDP next r hr) p = Measure.dirac (next p.1 p.2) := by
  rw [mdpTransitionKernel]
  exact jao_transitionDist_det next r hr p.1 p.2

lemma jao_stateKernel_det (next : Fin S → Fin A → Fin S) (r) (hr) (f : Fin S → Fin A) (src : Fin S)
    (n : ℕ) :
    mdpStateKernel (jao_detMDP next r hr) (mdpStateDirac src) n (jao_path next f src n) =
      Measure.dirac (jao_pathState next f src n) := by
  cases n with
  | zero => simp [mdpStateKernel, jao_stateDirac_toMeasure, jao_pathState]
  | succ n =>
      rw [mdpStateKernel, Kernel.comap_apply, jao_transitionKernel_det]
      simp [jao_path, jao_pathState]

lemma jao_stepKernel_det (next : Fin S → Fin A → Fin S) (r) (hr) (f : Fin S → Fin A) (src : Fin S)
    (n : ℕ) :
    mdpStepKernel (jao_detMDP next r hr) (mdpStateDirac src) (mdpMemorylessDetPolicy f) n
        (jao_path next f src n) =
      Measure.dirac (jao_pathState next f src n, f (jao_pathState next f src n)) := by
  ext s hs
  rw [mdpStepKernel, Kernel.compProd_apply hs, jao_stateKernel_det, lintegral_dirac]
  simp only [mdpMemorylessDetPolicy]
  rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (measurable_prodMk_left hs),
    Measure.dirac_apply' _ hs]
  rfl

lemma jao_mdpMeasure_det (next : Fin S → Fin A → Fin S) (r) (hr) (f : Fin S → Fin A) (src : Fin S)
    (n : ℕ) :
    mdpMeasure (jao_detMDP next r hr) (mdpStateDirac src) (mdpMemorylessDetPolicy f) n =
      Measure.dirac (jao_path next f src n) := by
  induction n with
  | zero =>
      simp only [mdpMeasure]
      congr 1
      funext t
      exact t.elim0
  | succ n ih =>
      rw [mdpMeasure, ih]
      have hcomp : (Measure.dirac (jao_path next f src n)).compProd
          (mdpStepKernel (jao_detMDP next r hr) (mdpStateDirac src) (mdpMemorylessDetPolicy f) n) =
          Measure.dirac (jao_path next f src n,
            (jao_pathState next f src n, f (jao_pathState next f src n))) := by
        ext s hs
        rw [Measure.compProd_apply hs, lintegral_dirac, jao_stepKernel_det,
          Measure.dirac_apply' _ (measurable_prodMk_left hs), Measure.dirac_apply' _ hs]
        rfl
      rw [hcomp, Measure.map_dirac' measurable_mdpTrajectorySnoc]
      congr 1
      funext t
      simp only [jao_path]
      refine Fin.lastCases ?_ (fun i => ?_) t
      · simp [Fin.snoc]
      · simp [Fin.snoc, jao_path]

/-- The trajectory measure only depends on the transition function. -/
lemma jao_mdpMeasure_congr_P (M M' : FiniteMDP S A) (h : M.P = M'.P)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    mdpMeasure M μ0 π n = mdpMeasure M' μ0 π n := by
  have hT : mdpTransitionKernel M = mdpTransitionKernel M' := by
    obtain ⟨P, hP, r, hr⟩ := M
    obtain ⟨P', hP', r', hr'⟩ := M'
    simp only at h
    subst h
    rfl
  have hS : ∀ n, mdpStateKernel M μ0 n = mdpStateKernel M' μ0 n := by
    intro n
    cases n with
    | zero => rfl
    | succ n => rw [mdpStateKernel, mdpStateKernel, hT]
  have hStep : ∀ n, mdpStepKernel M μ0 π n = mdpStepKernel M' μ0 π n := by
    intro n
    rw [mdpStepKernel, mdpStepKernel, hS]
  induction n with
  | zero => rfl
  | succ n ih => rw [mdpMeasure, mdpMeasure, ih, hStep]

/-! ### Travel time and diameter of a deterministic MDP -/

lemma jao_travelTime_le (next : Fin S → Fin A → Fin S) (r) (hr) (f : Fin S → Fin A)
    (src tgt : Fin S) (j : ℕ) (hj : jao_pathState next f src j = tgt) :
    mdpTravelTime (jao_detMDP next r hr) f src tgt ≤ (j : ENNReal) := by
  unfold mdpTravelTime
  have hterm : ∀ k : ℕ,
      mdpMeasure (jao_detMDP next r hr) (mdpStateDirac src) (mdpMemorylessDetPolicy f) (k + 1)
        {h | ∀ t, (h t).1 ≠ tgt} ≤ if k < j then 1 else 0 := by
    intro k
    rw [jao_mdpMeasure_det, Measure.dirac_apply]
    split_ifs with hk
    · exact Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le_one)
    · rw [Set.indicator_of_notMem]
      intro hmem
      have := hmem ⟨j, by omega⟩
      exact this (by simpa [jao_path] using hj)
  calc ∑' k : ℕ, mdpMeasure (jao_detMDP next r hr) (mdpStateDirac src) (mdpMemorylessDetPolicy f)
          (k + 1) {h | ∀ t, (h t).1 ≠ tgt}
        ≤ ∑' k : ℕ, (if k < j then (1 : ENNReal) else 0) := ENNReal.tsum_le_tsum hterm
    _ = ∑ k ∈ Finset.range j, (if k < j then (1 : ENNReal) else 0) := by
        refine tsum_eq_sum (s := Finset.range j) ?_
        intro k hk
        simp only [Finset.mem_range, not_lt] at hk
        simp [not_lt.mpr hk]
    _ = (j : ENNReal) := by
        rw [Finset.sum_ite_of_true (fun k hk => Finset.mem_range.mp hk)]
        simp

lemma jao_diameter_le (next : Fin S → Fin A → Fin S) (r) (hr) (D : ℝ)
    (h : ∀ src tgt : Fin S, src ≠ tgt →
      ∃ f : Fin S → Fin A, ∃ j : ℕ, (j : ℝ) ≤ D ∧ jao_pathState next f src j = tgt) :
    mdpDiameterENN (jao_detMDP next r hr) ≤ ENNReal.ofReal D := by
  unfold mdpDiameterENN
  refine iSup_le fun src => iSup_le fun tgt => iSup_le fun hne => ?_
  obtain ⟨f, j, hjD, hj⟩ := h src tgt hne
  refine iInf_le_of_le f ?_
  refine (jao_travelTime_le next r hr f src tgt j hj).trans ?_
  rw [← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal hjD

/-! ### The optimal gain of an MDP with a rewarding self-loop -/

lemma jao_gain_le_one (M : FiniteMDP S A) (π : MDPPolicy S A) (s : Fin S) :
    mdpGain M π s ≤ 1 := by
  unfold mdpGain
  have hreward : ∀ n : ℕ, mdpExpectedReward M (mdpStateDirac s) π n ≤ n := by
    intro n
    unfold mdpExpectedReward
    calc ∫ h, mdpTrajectoryReward M h ∂(mdpMeasure M (mdpStateDirac s) π n)
        ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M (mdpStateDirac s) π n) := by
          refine integral_mono Integrable.of_finite Integrable.of_finite ?_
          intro h
          unfold mdpTrajectoryReward
          calc ∑ t, M.r (h t).1 (h t).2 ≤ ∑ _t : Fin n, (1 : ℝ) :=
                Finset.sum_le_sum fun t _ => (M.r_mem_Icc _ _).2
            _ = n := by simp
      _ = n := by simp
  have hnonneg : ∀ n : ℕ, 0 ≤ mdpExpectedReward M (mdpStateDirac s) π n := by
    intro n
    unfold mdpExpectedReward
    refine integral_nonneg fun h => ?_
    unfold mdpTrajectoryReward
    exact Finset.sum_nonneg fun t _ => (M.r_mem_Icc _ _).1
  refine Filter.limsup_le_of_le ?_ ?_
  · refine Filter.IsBoundedUnder.isCoboundedUnder_le ?_
    refine Filter.isBoundedUnder_of ⟨0, fun n => ?_⟩
    exact div_nonneg (hnonneg n) (Nat.cast_nonneg n)
  · refine Filter.Eventually.of_forall fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [div_le_one (by exact_mod_cast hn)]
      exact hreward n

lemma jao_optimalGain_ge_one (next : Fin S → Fin A → Fin S) (r) (hr) (s₀ : Fin S) (a₀ : Fin A)
    (hloop : next s₀ a₀ = s₀) (hr₀ : r s₀ a₀ = 1) :
    1 ≤ mdpOptimalGain (jao_detMDP next r hr) := by
  set M := jao_detMDP next r hr with hM
  haveI : Nonempty (MDPPolicy S A) := ⟨mdpMemorylessDetPolicy fun _ => a₀⟩
  have hpath : ∀ n, jao_pathState next (fun _ => a₀) s₀ n = s₀ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [jao_pathState, ih, hloop]
  have hgain : mdpGain M (mdpMemorylessDetPolicy fun _ => a₀) s₀ = 1 := by
    unfold mdpGain
    have hexp : ∀ n : ℕ,
        mdpExpectedReward M (mdpStateDirac s₀) (mdpMemorylessDetPolicy fun _ => a₀) n = n := by
      intro n
      unfold mdpExpectedReward
      rw [hM, jao_mdpMeasure_det, integral_dirac]
      unfold mdpTrajectoryReward
      simp [jao_path, hpath, jao_detMDP, hr₀]
    have heq : ∀ᶠ n : ℕ in Filter.atTop,
        mdpExpectedReward M (mdpStateDirac s₀) (mdpMemorylessDetPolicy fun _ => a₀) n / n =
          (1 : ℝ) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with n hn
      rw [hexp, div_self (by exact_mod_cast hn.ne')]
    rw [Filter.limsup_congr heq, Filter.limsup_const]
  have hbdd1 : BddAbove (Set.range fun π : MDPPolicy S A => mdpGain M π s₀) :=
    ⟨1, by rintro _ ⟨π, rfl⟩; exact jao_gain_le_one M π s₀⟩
  have hbdd2 : BddAbove (Set.range fun s : Fin S => ⨆ π : MDPPolicy S A, mdpGain M π s) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact ciSup_le fun π => jao_gain_le_one M π s
  unfold mdpOptimalGain
  calc (1 : ℝ) = mdpGain M (mdpMemorylessDetPolicy fun _ => a₀) s₀ := hgain.symm
    _ ≤ ⨆ π : MDPPolicy S A, mdpGain M π s₀ := le_ciSup hbdd1 _
    _ ≤ ⨆ s : Fin S, ⨆ π : MDPPolicy S A, mdpGain M π s := le_ciSup hbdd2 s₀

/-! ### Expected reward of an arbitrary policy for an indicator reward -/

/-- The indicator reward of a single (state, action) pair. -/
def jao_indReward (p : Fin S × Fin A) : Fin S → Fin A → ℝ :=
  fun s a => if (s, a) = p then 1 else 0

lemma jao_indReward_mem (p : Fin S × Fin A) : ∀ s a, jao_indReward p s a ∈ Set.Icc (0 : ℝ) 1 := by
  intro s a
  unfold jao_indReward
  split_ifs <;> simp

/-- The occupation weight of the pair `p` for the trajectory measure `μ` on `n` rounds. -/
noncomputable def jao_occ {n : ℕ} (μ : Measure (MDPTrajectory S A n)) (p : Fin S × Fin A) : ℝ :=
  ∑ t : Fin n, (μ {h | h t = p}).toReal

lemma jao_integral_indReward {n : ℕ} (μ : Measure (MDPTrajectory S A n)) [IsFiniteMeasure μ]
    (p : Fin S × Fin A) :
    ∫ h, (∑ t, jao_indReward p (h t).1 (h t).2) ∂μ = jao_occ μ p := by
  rw [integral_finsetSum _ (fun t _ => Integrable.of_finite)]
  unfold jao_occ
  refine Finset.sum_congr rfl fun t _ => ?_
  have : (fun h : MDPTrajectory S A n => jao_indReward p (h t).1 (h t).2) =
      Set.indicator {h : MDPTrajectory S A n | h t = p} 1 := by
    funext h
    simp only [jao_indReward, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
  rw [this, integral_indicator_one MeasurableSet.of_discrete]
  rfl

lemma jao_sum_occ {n : ℕ} (μ : Measure (MDPTrajectory S A n)) [IsProbabilityMeasure μ] :
    ∑ p : Fin S × Fin A, jao_occ μ p = n := by
  unfold jao_occ
  rw [Finset.sum_comm]
  have : ∀ t : Fin n, ∑ p : Fin S × Fin A, (μ {h | h t = p}).toReal = 1 := by
    intro t
    rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
    have h := sum_measure_preimage_singleton (μ := μ) (Finset.univ : Finset (Fin S × Fin A))
      (f := fun h : MDPTrajectory S A n => h t) (fun _ _ => MeasurableSet.of_discrete)
    simp only [Finset.coe_univ, Set.preimage_univ, measure_univ] at h
    rw [← ENNReal.toReal_one, ← h]
    congr 1
  simp [this]

lemma jao_occ_nonneg {n : ℕ} (μ : Measure (MDPTrajectory S A n)) (p : Fin S × Fin A) :
    0 ≤ jao_occ μ p :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- Two distinct pairs cannot both carry more than half of the occupation mass. -/
lemma jao_occ_pair_lt {n : ℕ} (μ : Measure (MDPTrajectory S A n)) [IsProbabilityMeasure μ]
    (hn : 0 < n) (θ : ℝ) (hθ : 1 / 2 < θ) (p q : Fin S × Fin A) (hpq : p ≠ q)
    (hp : θ * n ≤ jao_occ μ p) (hq : θ * n ≤ jao_occ μ q) : False := by
  have h1 : jao_occ μ p + jao_occ μ q ≤ ∑ p : Fin S × Fin A, jao_occ μ p := by
    rw [← Finset.sum_pair hpq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun x _ _ => jao_occ_nonneg μ x
  rw [jao_sum_occ] at h1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  nlinarith

/-- Pigeonhole: some self-loop pair `(s, 0)` or `(s, 1)` has small occupation from every start. -/
lemma jao_exists_uncovered_pair (hS : 0 < S) (hA : 2 ≤ A) (n : ℕ) (hn : 0 < n)
    (μ : Fin S → Measure (MDPTrajectory S A n)) [∀ s, IsProbabilityMeasure (μ s)]
    (θ : ℝ) (hθ : 1 / 2 < θ) :
    ∃ p : Fin S × Fin A, p.2.val ≤ 1 ∧ ∀ s, jao_occ (μ s) p < θ * n := by
  by_contra hcon
  push_neg at hcon
  let φ : Fin S ⊕ Fin S → Fin S × Fin A := fun x =>
    match x with
    | Sum.inl s => (s, ⟨0, by omega⟩)
    | Sum.inr s => (s, ⟨1, by omega⟩)
  have hφ : ∀ x, (φ x).2.val ≤ 1 := by
    rintro (s | s) <;> simp [φ]
  have hφinj : Function.Injective φ := by
    rintro (s | s) (s' | s') h <;> simp [φ, Prod.ext_iff, Fin.ext_iff] at h <;>
      simp only [Sum.inl.injEq, Sum.inr.injEq] <;> exact Fin.ext h
  choose c hc using fun x => hcon (φ x) (hφ x)
  obtain ⟨x, y, hxy, hcxy⟩ := Fintype.exists_ne_map_eq_of_card_lt c (by simp; omega)
  exact jao_occ_pair_lt (μ (c x)) hn θ hθ (φ x) (φ y) (fun h => hxy (hφinj h)) (hc x)
    (hcxy ▸ hc y)

/-! ### The navigation structure -/

/-- Transitions: actions `0,1` are self-loops, action `2` resets to state `0`, and action
`d + 3` appends the base-`(A-3)` jao_digit `d`. -/
def jao_nav (hS : 0 < S) : Fin S → Fin A → Fin S := fun s a =>
  if a.val ≤ 1 then s
  else if a.val = 2 then ⟨0, hS⟩
  else if h : s.val * (A - 3) + (a.val - 3) < S then ⟨_, h⟩ else ⟨0, hS⟩

/-- The jao_digit action. -/
def jao_digit (hA : 10 ≤ A) (d : ℕ) : Fin A :=
  ⟨d % (A - 3) + 3, by have := Nat.mod_lt d (show 0 < A - 3 by omega); omega⟩

/-- The jao_reset action. -/
def jao_reset (hA : 10 ≤ A) : Fin A := ⟨2, by omega⟩

open Classical in
/-- The memoryless policy steering towards `tgt`. -/
noncomputable def jao_pol (hA : 10 ≤ A) (tgt : Fin S) : Fin S → Fin A := fun s =>
  if s.val = 0 then jao_digit hA (tgt.val / (A - 3) ^ (Nat.log (A - 3) tgt.val))
  else if ∃ m, 1 ≤ m ∧ tgt.val / (A - 3) ^ m = s.val then
    jao_digit hA ((tgt.val / (A - 3) ^ (Nat.log (A - 3) tgt.val - Nat.log (A - 3) s.val - 1)) %
      (A - 3))
  else jao_reset hA

/-- The `m`-th prefix state of `tgt`. -/
def jao_pre (tgt : Fin S) (B m : ℕ) : Fin S :=
  ⟨tgt.val / B ^ m, lt_of_le_of_lt (Nat.div_le_self _ _) tgt.isLt⟩

lemma jao_nav_digit (hS : 0 < S) (hA : 10 ≤ A) (s : Fin S) (d : ℕ) (hd : d < A - 3)
    (hlt : s.val * (A - 3) + d < S) :
    jao_nav hS s (jao_digit hA d) = ⟨s.val * (A - 3) + d, hlt⟩ := by
  have hd' : (jao_digit hA d).val = d + 3 := by simp [jao_digit, Nat.mod_eq_of_lt hd]
  unfold jao_nav
  rw [hd']
  have h1 : ¬ (d + 3 ≤ 1) := by omega
  have h2 : ¬ (d + 3 = 2) := by omega
  simp only [h1, h2, if_false, Nat.add_sub_cancel]
  rw [dif_pos hlt]

lemma jao_nav_reset (hS : 0 < S) (hA : 10 ≤ A) (s : Fin S) :
    jao_nav hS s (jao_reset hA) = ⟨0, hS⟩ := by
  unfold jao_nav jao_reset
  simp

lemma jao_nav_loop (hS : 0 < S) (s : Fin S) (a : Fin A) (ha : a.val ≤ 1) :
    jao_nav hS s a = s := by
  unfold jao_nav
  simp [ha]

/-- One jao_descent step along the prefix chain of `tgt`. -/
lemma jao_descent (hS : 0 < S) (hA : 10 ≤ A) (tgt : Fin S) (m : ℕ) (hm1 : 1 ≤ m)
    (hm2 : m ≤ Nat.log (A - 3) tgt.val + 1) :
    jao_nav hS (jao_pre tgt (A - 3) m) (jao_pol hA tgt (jao_pre tgt (A - 3) m)) = jao_pre tgt (A - 3) (m - 1) := by
  have hB1 : 1 < A - 3 := by omega
  have hBpos : 0 < A - 3 := by omega
  have hpre_lt : ∀ k, tgt.val / (A - 3) ^ k < S := fun k => (jao_pre tgt (A - 3) k).isLt
  by_cases h0 : tgt.val / (A - 3) ^ m = 0
  · -- the state is `0`: play the leading jao_digit
    have hpol : jao_pol hA tgt (jao_pre tgt (A - 3) m) =
        jao_digit hA (tgt.val / (A - 3) ^ (Nat.log (A - 3) tgt.val)) := by
      unfold jao_pol
      simp only [jao_pre, h0, if_true]
    have hlead : tgt.val / (A - 3) ^ (Nat.log (A - 3) tgt.val) < A - 3 := by
      rw [Nat.div_lt_iff_lt_mul (pow_pos hBpos _), ← pow_succ']
      exact Nat.lt_pow_succ_log_self hB1 _
    have hm : m - 1 = Nat.log (A - 3) tgt.val := by
      rcases Nat.eq_zero_or_pos tgt.val with ht | ht
      · have : Nat.log (A - 3) tgt.val = 0 := by simp [ht]
        omega
      · have : Nat.log (A - 3) tgt.val < m :=
          Nat.log_lt_of_lt_pow ht.ne' (Nat.lt_of_div_eq_zero (pow_pos hBpos m) h0)
        omega
    have hlt0 : (jao_pre tgt (A - 3) m).val * (A - 3) +
        tgt.val / (A - 3) ^ (Nat.log (A - 3) tgt.val) < S := by
      simp only [jao_pre, h0, Nat.zero_mul, Nat.zero_add]
      exact hpre_lt _
    rw [hpol, jao_nav_digit hS hA _ _ hlead hlt0]
    ext
    simp only [jao_pre, h0, Nat.zero_mul, Nat.zero_add, hm]
  · -- the state is a nonzero prefix: play the next jao_digit
    have hBm : (A - 3) ^ m ≤ tgt.val := by
      by_contra hcon
      exact h0 (Nat.div_eq_of_lt (not_le.mp hcon))
    have ht0 : tgt.val ≠ 0 := by
      intro ht
      rw [ht] at hBm
      exact absurd hBm (not_le.mpr (pow_pos hBpos m))
    have hmL : m ≤ Nat.log (A - 3) tgt.val := Nat.le_log_of_pow_le hB1 hBm
    have hlog : Nat.log (A - 3) (tgt.val / (A - 3) ^ m) = Nat.log (A - 3) tgt.val - m := by
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · rw [Nat.le_div_iff_mul_le (pow_pos hBpos m), ← pow_add, Nat.sub_add_cancel hmL]
        exact Nat.pow_log_le_self (A - 3) ht0
      · rw [Nat.div_lt_iff_lt_mul (pow_pos hBpos m), ← pow_add]
        have : Nat.log (A - 3) tgt.val - m + 1 + m = Nat.log (A - 3) tgt.val + 1 := by omega
        rw [this]
        exact Nat.lt_pow_succ_log_self hB1 _
    have hex : ∃ k, 1 ≤ k ∧ tgt.val / (A - 3) ^ k = tgt.val / (A - 3) ^ m := ⟨m, hm1, rfl⟩
    have hpol : jao_pol hA tgt (jao_pre tgt (A - 3) m) =
        jao_digit hA ((tgt.val / (A - 3) ^ (m - 1)) % (A - 3)) := by
      unfold jao_pol
      simp only [jao_pre]
      rw [if_neg h0, if_pos hex, hlog]
      have hidx : Nat.log (A - 3) tgt.val - (Nat.log (A - 3) tgt.val - m) - 1 = m - 1 := by
        omega
      rw [hidx]
    have hdig : (tgt.val / (A - 3) ^ (m - 1)) % (A - 3) < A - 3 := Nat.mod_lt _ hBpos
    have hval : (tgt.val / (A - 3) ^ m) * (A - 3) + (tgt.val / (A - 3) ^ (m - 1)) % (A - 3) =
        tgt.val / (A - 3) ^ (m - 1) := by
      have h1 : tgt.val / (A - 3) ^ m = tgt.val / (A - 3) ^ (m - 1) / (A - 3) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel hm1]
      rw [h1, mul_comm]
      exact Nat.div_add_mod _ _
    rw [hpol, jao_nav_digit hS hA _ _ hdig (by simp only [jao_pre]; rw [hval]; exact hpre_lt _)]
    ext
    simp only [jao_pre, hval]

lemma jao_pathState_pre (hS : 0 < S) (hA : 10 ≤ A) (tgt : Fin S) (m : ℕ)
    (hm2 : m ≤ Nat.log (A - 3) tgt.val + 1) (i : ℕ) (hi : i ≤ m) :
    jao_pathState (jao_nav hS) (jao_pol hA tgt) (jao_pre tgt (A - 3) m) i = jao_pre tgt (A - 3) (m - i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [jao_pathState, ih (by omega)]
      have := jao_descent hS hA tgt (m - i) (by omega) (by omega)
      rw [this, Nat.sub_sub]

lemma jao_pre_zero (tgt : Fin S) (B : ℕ) : jao_pre tgt B 0 = tgt := by
  ext; simp [jao_pre]

lemma jao_pre_top (hA : 10 ≤ A) (hS : 0 < S) (tgt : Fin S) :
    jao_pre tgt (A - 3) (Nat.log (A - 3) tgt.val + 1) = ⟨0, hS⟩ := by
  ext
  simp only [jao_pre]
  exact Nat.div_eq_of_lt (Nat.lt_pow_succ_log_self (by omega) _)

/-- From every source, the policy `jao_pol tgt` jao_reaches `tgt` within `log tgt + 2` steps. -/
lemma jao_reaches (hS : 0 < S) (hA : 10 ≤ A) (src tgt : Fin S) (hne : src ≠ tgt) :
    ∃ j : ℕ, j ≤ Nat.log (A - 3) tgt.val + 2 ∧
      jao_pathState (jao_nav hS) (jao_pol hA tgt) src j = tgt := by
  by_cases h0 : src.val = 0
  · refine ⟨Nat.log (A - 3) tgt.val + 1, by omega, ?_⟩
    have hsrc : src = jao_pre tgt (A - 3) (Nat.log (A - 3) tgt.val + 1) := by
      rw [jao_pre_top hA hS]; ext; exact h0
    rw [hsrc, jao_pathState_pre hS hA tgt _ le_rfl _ le_rfl, Nat.sub_self, jao_pre_zero]
  · by_cases hex : ∃ m, 1 ≤ m ∧ tgt.val / (A - 3) ^ m = src.val
    · obtain ⟨m, hm1, hm⟩ := hex
      have hsrc : src = jao_pre tgt (A - 3) m := by ext; exact hm.symm
      have hBm : (A - 3) ^ m ≤ tgt.val := by
        by_contra hcon
        exact h0 (hm ▸ Nat.div_eq_of_lt (not_le.mp hcon))
      have hmL : m ≤ Nat.log (A - 3) tgt.val := Nat.le_log_of_pow_le (by omega) hBm
      refine ⟨m, by omega, ?_⟩
      rw [hsrc, jao_pathState_pre hS hA tgt m (by omega) m le_rfl, Nat.sub_self, jao_pre_zero]
    · refine ⟨1 + (Nat.log (A - 3) tgt.val + 1), by omega, ?_⟩
      rw [jao_pathState_add]
      have h1 : jao_pathState (jao_nav hS) (jao_pol hA tgt) src 1 =
          jao_pre tgt (A - 3) (Nat.log (A - 3) tgt.val + 1) := by
        rw [jao_pre_top hA hS]
        show jao_nav hS src (jao_pol hA tgt src) = _
        have hpol : jao_pol hA tgt src = jao_reset hA := by
          unfold jao_pol
          rw [if_neg h0, if_neg hex]
        rw [hpol, jao_nav_reset]
      rw [h1, jao_pathState_pre hS hA tgt _ le_rfl _ le_rfl, Nat.sub_self, jao_pre_zero]


/-! ### Real-analytic bounds -/

lemma jao_log_bound (S A : ℕ) (D : ℝ) (hS : 10 ≤ S) (hA : 10 ≤ A)
    (hD : 20 * (Real.log S / Real.log A) ≤ D) (hD12 : 12 ≤ D) (tgt : ℕ) (htgt : tgt < S) :
    ((Nat.log (A - 3) tgt + 2 : ℕ) : ℝ) ≤ D := by
  set B := A - 3 with hB
  set L := Nat.log B tgt with hL
  have hBpos : (0 : ℝ) < B := by
    have : 7 ≤ B := by omega
    exact_mod_cast (show 0 < B by omega)
  have hBcast : (B : ℝ) = (A : ℝ) - 3 := by
    rw [hB, Nat.cast_sub (by omega)]; simp
  have hA' : (10 : ℝ) ≤ A := by exact_mod_cast hA
  have hB7 : (7 : ℝ) ≤ B := by rw [hBcast]; linarith
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hlogA : 0 < Real.log A := Real.log_pos (by linarith)
  have hS' : (10 : ℝ) ≤ S := by exact_mod_cast hS
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  -- `B ^ L ≤ S`
  have hpow : (B : ℝ) ^ L ≤ S := by
    rcases Nat.eq_zero_or_pos tgt with ht | ht
    · have : L = 0 := by simp [hL, ht]
      rw [this, pow_zero]; linarith
    · have h1 : B ^ L ≤ tgt := Nat.pow_log_le_self B ht.ne'
      have h2 : ((B ^ L : ℕ) : ℝ) ≤ S := by exact_mod_cast (h1.trans htgt.le)
      simpa using h2
  have hLlog : (L : ℝ) * Real.log B ≤ Real.log S := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpow
  have hL1 : (L : ℝ) ≤ Real.log S / Real.log B := by
    rw [le_div_iff₀ hlogB]; exact hLlog
  -- `A ≤ B ^ 2`
  have hAB : (A : ℝ) ≤ (B : ℝ) ^ 2 := by rw [hBcast]; nlinarith
  have hlogAB : Real.log A ≤ 2 * Real.log B := by
    have := Real.log_le_log (by linarith) hAB
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hL2 : Real.log S / Real.log B ≤ 2 * Real.log S / Real.log A := by
    rw [div_le_div_iff₀ hlogB hlogA]
    nlinarith
  have hL3 : 2 * Real.log S / Real.log A ≤ D / 10 := by
    have : 2 * Real.log S / Real.log A = (20 * (Real.log S / Real.log A)) / 10 := by ring
    rw [this]; linarith
  push_cast
  linarith

lemma jao_sqrt_bound (S A T : ℕ) (D : ℝ) (hD : 0 ≤ D) (hT : D * S * A ≤ (T : ℝ)) :
    Real.sqrt (D * S * A * T) ≤ T := by
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  calc Real.sqrt (D * S * A * T) ≤ Real.sqrt (T * T) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hT hT0)
    _ = T := Real.sqrt_mul_self hT0


open BanditAlgorithm in
theorem solution :
    ∀ S A T : ℕ, ∀ D : ℝ, 10 ≤ S → 10 ≤ A →
      20 * (Real.log S / Real.log A) ≤ D → D * S * A ≤ (T : ℝ) → 12 ≤ D →
        ∀ π : MDPPolicy S A,
          ∃ M : FiniteMDP S A,
            mdpDiameterENN M ≤ ENNReal.ofReal D ∧
            ∀ s : Fin S,
              0.015 * Real.sqrt (D * S * A * T) ≤
                ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) := by
  intro S A T D hS hA hD hT hD12 π
  have hS0 : 0 < S := by omega
  have hA2 : 2 ≤ A := by omega
  -- the transition structure (independent of the reward)
  let next := jao_nav (A := A) hS0
  -- horizon is positive
  have hTpos : 0 < T := by
    have hS' : (10 : ℝ) ≤ S := by exact_mod_cast hS
    have hA' : (10 : ℝ) ≤ A := by exact_mod_cast hA
    have hD0 : (0 : ℝ) ≤ D := by linarith
    have hDS : (12 : ℝ) * 10 ≤ D * S := mul_le_mul hD12 hS' (by norm_num) hD0
    have h1 : (12 : ℝ) * 10 * 10 ≤ D * S * A :=
      mul_le_mul hDS hA' (by norm_num) (by positivity)
    have : (0 : ℝ) < T := by linarith
    exact_mod_cast this
  -- pick the uncovered self-loop pair using the reward-free MDP
  let M₀ := jao_detMDP next (fun _ _ => 0) (fun _ _ => by simp)
  obtain ⟨p, hp1, hp⟩ := jao_exists_uncovered_pair hS0 hA2 T hTpos
    (fun s => mdpMeasure M₀ (mdpStateDirac s) π T) (0.985) (by norm_num)
  let M := jao_detMDP next (jao_indReward p) (jao_indReward_mem p)
  refine ⟨M, ?_, ?_⟩
  · -- diameter
    apply jao_diameter_le
    intro src tgt hne
    obtain ⟨j, hj, hpath⟩ := jao_reaches hS0 hA src tgt hne
    refine ⟨jao_pol hA tgt, j, ?_, hpath⟩
    calc (j : ℝ) ≤ ((Nat.log (A - 3) tgt.val + 2 : ℕ) : ℝ) := by exact_mod_cast hj
      _ ≤ D := jao_log_bound S A D hS hA hD hD12 tgt.val tgt.isLt
  · -- regret
    intro s
    have hmeas : mdpMeasure M (mdpStateDirac s) π T = mdpMeasure M₀ (mdpStateDirac s) π T :=
      jao_mdpMeasure_congr_P M M₀ rfl _ _ _
    have hgain : 1 ≤ mdpOptimalGain M :=
      jao_optimalGain_ge_one next _ _ p.1 p.2 (jao_nav_loop hS0 p.1 p.2 hp1)
        (by simp [jao_indReward])
    have hint : ∫ h, mdpRegret M T h ∂(mdpMeasure M (mdpStateDirac s) π T) =
        T * mdpOptimalGain M - jao_occ (mdpMeasure M₀ (mdpStateDirac s) π T) p := by
      unfold mdpRegret
      rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const]
      simp only [probReal_univ, one_smul]
      rw [hmeas]
      congr 1
      exact jao_integral_indReward _ p
    rw [hint]
    have hocc := hp s
    have hsqrt := jao_sqrt_bound S A T D (by linarith) hT
    have hT' : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    nlinarith
