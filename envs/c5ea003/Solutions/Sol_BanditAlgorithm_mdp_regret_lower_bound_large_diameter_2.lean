-- Prove2me | solution 2 for BanditAlgorithm.mdp_regret_lower_bound_large_diameter
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T08:56:01.186937+00:00
-- url     : https://prove2.me/submissions/99709999-eec7-483a-913d-16979f1cf737

import Definitions.Def_FiniteMDPLearning
import Theorems.Thm_BanditAlgorithm_mdp_travel_time_le_of_lyapunov_drift
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_ge_of_reverse_bellman_ineq
import Theorems.Thm_BanditAlgorithm_mdp_optimal_gain_le_of_bellman_ineq
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped NNReal ENNReal

variable {S A : ℕ}

/-- Successor map of the `A`-ary heap on `Fin S`, with overflow reset to the root `0`:
the `a`-th child of `s` is `A * s + 1 + a` when that index is a state, otherwise the root. -/
def heapNext (hS : 0 < S) (s : Fin S) (a : Fin A) : Fin S :=
  if h : A * s + 1 + a < S then ⟨A * s + 1 + a, h⟩ else ⟨0, hS⟩

/-- The deterministic transition row concentrated on `heapNext`. -/
def heapP (hS : 0 < S) (s : Fin S) (a : Fin A) : Fin S → ℝ≥0 :=
  fun s' => if s' = heapNext hS s a then 1 else 0

lemma heapP_sum_one (hS : 0 < S) (s : Fin S) (a : Fin A) :
    ∑ s', heapP hS s a s' = 1 := by
  simp [heapP]

lemma sum_heapP_mul (hS : 0 < S) (s : Fin S) (a : Fin A) (V : Fin S → ℝ) :
    ∑ s', ((heapP hS s a s' : ℝ≥0) : ℝ) * V s' = V (heapNext hS s a) := by
  rw [Finset.sum_eq_single (heapNext hS s a)]
  · simp [heapP]
  · intro b _ hb
    simp [heapP, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The MDP with heap transitions and reward `1` exactly for the action `a₀`. -/
def heapMDP (hS : 0 < S) (a₀ : Fin A) : FiniteMDP S A where
  P := heapP hS
  P_sum_one := heapP_sum_one hS
  r := fun _ a => if a = a₀ then 1 else 0
  r_mem_Icc := by
    intro s a
    split_ifs <;> simp

lemma mdpStepKernel_heapMDP (hS : 0 < S) (a₀ a₁ : Fin A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) :
    mdpStepKernel (heapMDP hS a₀) μ0 π = mdpStepKernel (heapMDP hS a₁) μ0 π := by
  funext m
  cases m <;> rfl

/-- The trajectory law does not depend on the rewards. -/
lemma mdpMeasure_heapMDP (hS : 0 < S) (a₀ a₁ : Fin A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) :
    mdpMeasure (heapMDP hS a₀) μ0 π n = mdpMeasure (heapMDP hS a₁) μ0 π n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mdpMeasure, mdpMeasure, ih, mdpStepKernel_heapMDP hS a₀ a₁]

/-- Drift certificate: for every target there are a memoryless deterministic policy and a
Lyapunov function, bounded by `(log_A S + 1) + log_A (A * tgt + 1)`, decreasing by one
along every transition away from the target. -/
lemma heapMDP_exists_lyapunov (hS : 0 < S) (hA : 2 ≤ A) (tgt : ℕ) (htgt : tgt < S) :
    ∃ (f : Fin S → Fin A) (V : Fin S → ℝ),
      (∀ s, 0 ≤ V s) ∧
      (∀ s, V s ≤ ((Nat.log A S + 1 : ℕ) : ℝ) + ((Nat.log A (A * tgt + 1) : ℕ) : ℝ)) ∧
      (∀ s : Fin S, (s : ℕ) ≠ tgt → V (heapNext hS s (f s)) + 1 ≤ V s) := by
  have hA1 : 1 < A := by omega
  have hApos : 0 < A := by omega
  induction tgt using Nat.strong_induction_on with
  | _ tgt ih =>
  rcases Nat.eq_zero_or_pos tgt with h0 | hpos
  · subst h0
    refine ⟨fun _ => ⟨0, hApos⟩,
      fun s => if (s : ℕ) = 0 then 0 else ((Nat.log A S + 1 : ℕ) : ℝ) - (Nat.log A s : ℝ),
      ?_, ?_, ?_⟩
    · intro s
      dsimp only
      split_ifs with hs
      · exact le_rfl
      · have h1 : Nat.log A s ≤ Nat.log A S := Nat.log_mono_right s.isLt.le
        have h2 : (Nat.log A s : ℝ) ≤ Nat.log A S := by exact_mod_cast h1
        push_cast
        linarith
    · intro s
      dsimp only
      have h3 : (0:ℝ) ≤ ((Nat.log A (A * 0 + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
      split_ifs with hs
      · positivity
      · have : (0:ℝ) ≤ Nat.log A s := Nat.cast_nonneg _
        linarith
    · intro s hs
      dsimp only
      have hnext : heapNext hS s ⟨0, hApos⟩ =
          if h : A * s + 1 < S then ⟨A * s + 1, h⟩ else ⟨0, hS⟩ := by
        simp [heapNext]
      rw [hnext, if_neg hs]
      have h1 : Nat.log A s ≤ Nat.log A S := Nat.log_mono_right s.isLt.le
      have h2 : (Nat.log A s : ℝ) ≤ Nat.log A S := by exact_mod_cast h1
      by_cases h : A * s + 1 < S
      · rw [dif_pos h]
        have hne : ((⟨A * s + 1, h⟩ : Fin S) : ℕ) ≠ 0 := by simp
        rw [if_neg hne]
        have h3 : Nat.log A s + 1 ≤ Nat.log A (A * s + 1) := by
          rw [← Nat.log_mul_base hA1 hs]
          apply Nat.log_mono_right
          rw [mul_comm]
          exact Nat.le_succ _
        have h4 : (Nat.log A s : ℝ) + 1 ≤ Nat.log A (A * s + 1) := by exact_mod_cast h3
        have h5 : ((⟨A * s + 1, h⟩ : Fin S) : ℕ) = A * s + 1 := rfl
        rw [h5]
        push_cast
        linarith
      · rw [dif_neg h]
        have hz : ((⟨0, hS⟩ : Fin S) : ℕ) = 0 := rfl
        rw [if_pos hz]
        push_cast
        linarith
  · set p := (tgt - 1) / A with hp_def
    set d := (tgt - 1) % A with hd_def
    have hpd : A * p + d = tgt - 1 := Nat.div_add_mod (tgt - 1) A
    have hp_lt : p < tgt := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hd_lt : d < A := Nat.mod_lt _ hApos
    have hp1 : A * p + 1 ≤ tgt := by omega
    obtain ⟨f, V, hV0, hVb, hdrift⟩ := ih p hp_lt (by omega)
    refine ⟨fun s => if (s : ℕ) = p then ⟨d, hd_lt⟩ else f s,
      fun s => if (s : ℕ) = tgt then 0 else V s + 1, ?_, ?_, ?_⟩
    · intro s
      dsimp only
      split_ifs
      · exact le_rfl
      · linarith [hV0 s]
    · intro s
      have key : Nat.log A (A * p + 1) + 1 ≤ Nat.log A (A * tgt + 1) := by
        rw [← Nat.log_mul_base hA1 (by omega)]
        apply Nat.log_mono_right
        calc (A * p + 1) * A ≤ tgt * A := Nat.mul_le_mul_right A hp1
          _ = A * tgt := mul_comm _ _
          _ ≤ A * tgt + 1 := Nat.le_succ _
      have h2 : ((Nat.log A (A * p + 1) : ℕ) : ℝ) + 1 ≤ ((Nat.log A (A * tgt + 1) : ℕ) : ℝ) := by
        exact_mod_cast key
      have h1 := hVb s
      dsimp only
      split_ifs with hs
      · positivity
      · linarith
    · intro s hs
      dsimp only
      by_cases hsp : (s : ℕ) = p
      · have hlt : A * (s : ℕ) + 1 + d < S := by rw [hsp]; omega
        have hnext : heapNext hS s ⟨d, hd_lt⟩ = ⟨tgt, htgt⟩ := by
          unfold heapNext
          simp only [Fin.val_mk]
          rw [dif_pos hlt]
          ext
          simp only [Fin.val_mk]
          rw [hsp]
          omega
        rw [if_pos hsp, hnext, if_neg hs]
        simp only [Fin.val_mk, if_true]
        linarith [hV0 s]
      · rw [if_neg hsp, if_neg hs]
        have hd := hdrift s hsp
        split_ifs with h
        · linarith [hV0 s]
        · linarith

/-- The diameter of the heap MDP is at most `2 log_A S + 2`. -/
lemma mdpDiameterENN_heapMDP_le (hS : 0 < S) (hA : 2 ≤ A) (a₀ : Fin A) :
    mdpDiameterENN (heapMDP hS a₀) ≤ ENNReal.ofReal (2 * (Nat.log A S : ℝ) + 2) := by
  have hA1 : 1 < A := by omega
  unfold mdpDiameterENN
  refine iSup_le fun src => iSup_le fun tgt => iSup_le fun _ => ?_
  obtain ⟨f, V, hV0, hVb, hdrift⟩ := heapMDP_exists_lyapunov hS hA tgt tgt.isLt
  refine (iInf_le _ f).trans ?_
  refine (BanditAlgorithm.mdp_travel_time_le_of_lyapunov_drift (heapMDP hS a₀) f src tgt V hV0
    ?_).trans ?_
  · intro s hs
    have h := hdrift s (fun h => hs (Fin.ext h))
    have : ∑ s', ((heapMDP hS a₀).P s (f s) s' : ℝ) * V s' = V (heapNext hS s (f s)) :=
      sum_heapP_mul hS s (f s) V
    rw [this]
    exact h
  · apply ENNReal.ofReal_le_ofReal
    have h1 := hVb src
    have h2 : Nat.log A (A * tgt + 1) ≤ Nat.log A S + 1 := by
      rw [← Nat.log_mul_base hA1 hS.ne']
      apply Nat.log_mono_right
      have := tgt.isLt
      calc A * (tgt : ℕ) + 1 ≤ A * tgt + A := by omega
        _ = A * (tgt + 1) := by ring
        _ ≤ A * S := Nat.mul_le_mul_left A tgt.isLt
        _ = S * A := mul_comm _ _
    have h3 : ((Nat.log A (A * tgt + 1) : ℕ) : ℝ) ≤ (Nat.log A S : ℝ) + 1 := by exact_mod_cast h2
    push_cast at h1
    linarith

/-- The optimal gain of the heap MDP is `1`. -/
lemma mdpOptimalGain_heapMDP (hS : 0 < S) (hA : 0 < A) (a₀ : Fin A) :
    mdpOptimalGain (heapMDP hS a₀) = 1 := by
  apply le_antisymm
  · refine BanditAlgorithm.mdp_optimal_gain_le_of_bellman_ineq hS hA (heapMDP hS a₀) 1
      (fun _ => 0) 0 0 (fun _ => ⟨le_rfl, le_rfl⟩) ?_
    intro s a
    simp only [heapMDP, mul_zero, Finset.sum_const_zero, add_zero]
    split_ifs <;> norm_num
  · refine BanditAlgorithm.mdp_optimal_gain_ge_of_reverse_bellman_ineq hS (heapMDP hS a₀)
      (fun _ => a₀) 1 (fun _ => 0) 0 0 (fun _ => ⟨le_rfl, le_rfl⟩) ?_
    intro s
    simp [heapMDP]

lemma heapMDP_sum_toReal_singleton (hS : 0 < S) (a₀ : Fin A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) :
    ∑ x : MDPTrajectory S A n, ((mdpMeasure (heapMDP hS a₀) μ0 π n) {x}).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp

/-- The expected regret of the heap MDP: `n` minus the expected number of plays of `a₀`. -/
lemma heapMDP_integral_regret (hS : 0 < S) (hA : 0 < A) (a₀ : Fin A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) :
    ∫ h, mdpRegret (heapMDP hS a₀) n h ∂(mdpMeasure (heapMDP hS a₀) μ0 π n)
      = n - ∑ x : MDPTrajectory S A n, ((mdpMeasure (heapMDP hS a₀) μ0 π n) {x}).toReal *
          ∑ t : Fin n, (if (x t).2 = a₀ then (1:ℝ) else 0) := by
  rw [integral_fintype Integrable.of_finite]
  have hsum := heapMDP_sum_toReal_singleton hS a₀ μ0 π n
  have hr : ∀ (s : Fin S) (a : Fin A), (heapMDP hS a₀).r s a = if a = a₀ then 1 else 0 :=
    fun _ _ => rfl
  simp only [mdpRegret, mdpOptimalGain_heapMDP hS hA a₀, mdpTrajectoryReward, hr,
    smul_eq_mul, mul_one, mul_sub, measureReal_def]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ S A n : ℕ, ∀ D : ℝ, 3 ≤ S → 2 ≤ A →
        20 * (1 + Real.log S / Real.log A) ≤ D → D * S * A ≤ n →
        ∀ π : MDPPolicy S A,
          ∃ M : FiniteMDP S A, ∃ μ0 : MDPStateDistribution S,
            mdpDiameterENN M ≤ ENNReal.ofReal D ∧
            C * Real.sqrt (D * S * A * n) ≤
              ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) := by
  refine ⟨1/2, by norm_num, ?_⟩
  intro S A n D hS3 hA2 hD hn π
  have hS : 0 < S := by omega
  have hA : 0 < A := by omega
  have hA1 : 1 < A := by omega
  -- the diameter budget dominates `2 log_A S + 2`
  have hlogA : 0 < Real.log A := Real.log_pos (by exact_mod_cast hA1)
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg (by exact_mod_cast (show 1 ≤ S by omega))
  have hratio : 0 ≤ Real.log S / Real.log A := div_nonneg hlogS hlogA.le
  have hNatlog : (Nat.log A S : ℝ) ≤ Real.log S / Real.log A := by
    rw [le_div_iff₀ hlogA]
    have h1 : A ^ Nat.log A S ≤ S := Nat.pow_log_le_self A hS.ne'
    have h2 : ((A:ℝ) ^ Nat.log A S) ≤ (S:ℝ) := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rwa [Real.log_pow] at h3
  have hdiam : (2 * (Nat.log A S : ℝ) + 2) ≤ D := by linarith
  -- the trajectory law of the heap MDP (independent of the rewards)
  set a₀ : Fin A := ⟨0, hA⟩ with ha₀
  set μ0 : MDPStateDistribution S := mdpStateDirac ⟨0, hS⟩ with hμ0
  set μ := mdpMeasure (heapMDP hS a₀) μ0 π n with hμ
  set cnt : Fin A → ℝ := fun a => ∑ x : MDPTrajectory S A n,
    (μ {x}).toReal * ∑ t : Fin n, (if (x t).2 = a then (1:ℝ) else 0) with hcnt
  have hsum : ∑ x : MDPTrajectory S A n, (μ {x}).toReal = 1 :=
    heapMDP_sum_toReal_singleton hS a₀ μ0 π n
  have hinner : ∀ x : MDPTrajectory S A n,
      ∑ a : Fin A, ∑ t : Fin n, (if (x t).2 = a then (1:ℝ) else 0) = n := by
    intro x
    rw [Finset.sum_comm]
    simp
  have hcnt_sum : ∑ a, cnt a = n := by
    calc ∑ a, cnt a
        = ∑ a : Fin A, ∑ x : MDPTrajectory S A n,
            (μ {x}).toReal * ∑ t : Fin n, (if (x t).2 = a then (1:ℝ) else 0) := rfl
      _ = ∑ x : MDPTrajectory S A n, ∑ a : Fin A,
            (μ {x}).toReal * ∑ t : Fin n, (if (x t).2 = a then (1:ℝ) else 0) :=
            Finset.sum_comm
      _ = ∑ x : MDPTrajectory S A n, (μ {x}).toReal * ∑ a : Fin A,
            ∑ t : Fin n, (if (x t).2 = a then (1:ℝ) else 0) := by
            simp_rw [Finset.mul_sum]
      _ = ∑ x : MDPTrajectory S A n, (μ {x}).toReal * n := by simp_rw [hinner]
      _ = n := by rw [← Finset.sum_mul, hsum, one_mul]
  -- the least played action
  obtain ⟨a₁, -, ha₁⟩ := Finset.exists_min_image Finset.univ cnt ⟨a₀, Finset.mem_univ a₀⟩
  have hcnt_le : (A : ℝ) * cnt a₁ ≤ n := by
    have := Finset.card_nsmul_le_sum Finset.univ cnt (cnt a₁)
      (fun a _ => ha₁ a (Finset.mem_univ a))
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcnt_sum] at this
    exact this
  have hcnt0 : 0 ≤ cnt a₁ :=
    Finset.sum_nonneg fun x _ => mul_nonneg ENNReal.toReal_nonneg
      (Finset.sum_nonneg fun t _ => by split_ifs <;> norm_num)
  refine ⟨heapMDP hS a₁, μ0, ?_, ?_⟩
  · exact (mdpDiameterENN_heapMDP_le hS hA2 a₁).trans (ENNReal.ofReal_le_ofReal hdiam)
  · rw [heapMDP_integral_regret hS hA a₁ μ0 π n, mdpMeasure_heapMDP hS a₁ a₀ μ0 π n]
    change (1/2 : ℝ) * Real.sqrt (D * S * A * n) ≤ n - cnt a₁
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have hsqrt : Real.sqrt (D * S * A * n) ≤ n := by
      calc Real.sqrt (D * S * A * n) ≤ Real.sqrt (n * n) :=
            Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hn hn0)
        _ = n := Real.sqrt_mul_self hn0
    have hA2r : (2:ℝ) ≤ A := by exact_mod_cast hA2
    have h2cnt : 2 * cnt a₁ ≤ n := by nlinarith
    linarith
