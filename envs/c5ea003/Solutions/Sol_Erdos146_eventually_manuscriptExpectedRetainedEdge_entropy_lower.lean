-- Prove2me | solution 1 for Erdos146.eventually_manuscriptExpectedRetainedEdge_entropy_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:45:12.639373+00:00
-- url     : https://prove2.me/submissions/7577ae21-f928-48dc-9c30-496f70bdd81d

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Real.StarOrdered
import Theorems.Thm_Erdos146_binomialProbabilityMass_nonneg
import Theorems.Thm_Erdos146_binomialProbabilityMass_succ_mul
import Theorems.Thm_Erdos146_hammingBall_card
import Theorems.Thm_Erdos146_hammingExpectedRetainedEdgeCount_eq
import Theorems.Thm_Erdos146_manuscriptHammingRadius_le
import Theorems.Thm_Erdos146_tau_lt_one_half

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem binomialModeRatio_le_of_lt
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hcount : successCount < mode) :
    ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) ≤
      ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub hmode,
    Nat.cast_sub (show successCount ≤ trialCount by omega),
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (mode : ℝ) - (successCount : ℝ) - 1 := by
    have hcast : (successCount : ℝ) + 1 ≤ (mode : ℝ) := by
      exact_mod_cast (show successCount + 1 ≤ mode by omega)
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_nonneg : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  nlinarith

theorem binomialModeRatio_le_of_ge
    (trialCount mode successCount : ℕ)
    (htrials : 0 < trialCount)
    (hmode : mode ≤ trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub (Nat.le_of_lt hsuccess),
    Nat.cast_sub hmode,
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (successCount : ℝ) - (mode : ℝ) := by
    have hcast : (mode : ℝ) ≤ (successCount : ℝ) := by
      exact_mod_cast hcount
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_le : (mode : ℝ) ≤ (trialCount : ℝ) := by
    exact_mod_cast hmode
  nlinarith

theorem binomialProbabilityMass_le_succ_of_lt_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : successCount < mode) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_lt
    trialCount mode successCount hmode.le hcount
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    (show successCount < trialCount by omega)
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) :=
        mul_le_mul_of_nonneg_left hratio hmass
    _ = binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]

theorem binomialProbabilityMass_succ_le_of_ge_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode < trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hprobability_zero :
      0 ≤ (mode : ℝ) / (trialCount : ℝ) := by positivity
  have hprobability_one :
      (mode : ℝ) / (trialCount : ℝ) < 1 := by
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode
  have hscale :
      0 < ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
    positivity
  have hmass := binomialProbabilityMass_nonneg
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ))
    hprobability_zero hprobability_one.le
  have hratio := binomialModeRatio_le_of_ge
    trialCount mode successCount htrials hmode.le hcount hsuccess
  have hidentity := binomialProbabilityMass_succ_mul
    trialCount successCount ((mode : ℝ) / (trialCount : ℝ)) hsuccess
  apply le_of_mul_le_mul_right (a :=
    ((successCount + 1 : ℕ) : ℝ) *
      (1 - (mode : ℝ) / (trialCount : ℝ)))
    (a0 := hscale)
  calc
    binomialProbabilityMass trialCount (successCount + 1)
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) =
      binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ))) := by
          nlinarith [hidentity]
    _ ≤ binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) *
      (((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ))) :=
          mul_le_mul_of_nonneg_left hratio hmass

theorem binomialProbabilityMass_le_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hsuccess : successCount ≤ trialCount) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  by_cases htrials : trialCount = 0
  · subst trialCount
    have hmode_zero : mode = 0 := by omega
    have hsuccess_zero : successCount = 0 := by omega
    subst mode
    subst successCount
    exact le_rfl
  by_cases hmode_zero : mode = 0
  · subst mode
    by_cases hsuccess_zero : successCount = 0
    · subst successCount
      exact le_rfl
    · simp [binomialProbabilityMass, hsuccess_zero]
  by_cases hmode_full : mode = trialCount
  · subst mode
    have htrials_real : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast htrials
    rw [div_self htrials_real]
    by_cases hsuccess_full : successCount = trialCount
    · subst successCount
      exact le_rfl
    · have hpositive : 0 < trialCount - successCount := by omega
      simp [binomialProbabilityMass, hpositive.ne']
  have hmode_lt : mode < trialCount := by omega
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hstep_up (index : ℕ) (hindex : index < mode) :
      binomialProbabilityMass trialCount index probability ≤
        binomialProbabilityMass trialCount (index + 1) probability := by
    exact binomialProbabilityMass_le_succ_of_lt_mode
      trialCount mode index hmode_lt hindex
  have hstep_down (index : ℕ)
      (hindex_mode : mode ≤ index)
      (hindex_trials : index < trialCount) :
      binomialProbabilityMass trialCount (index + 1) probability ≤
        binomialProbabilityMass trialCount index probability := by
    exact binomialProbabilityMass_succ_le_of_ge_mode
      trialCount mode index hmode_lt hindex_mode hindex_trials
  by_cases hbelow : successCount ≤ mode
  · have hwalk (index : ℕ) (hindex : successCount ≤ index) :
        index ≤ mode →
          binomialProbabilityMass trialCount successCount probability ≤
            binomialProbabilityMass trialCount index probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hinduction (by omega)).trans
          (hstep_up index (by omega))
    exact hwalk mode hbelow (le_refl mode)
  · have habove : mode ≤ successCount := by omega
    have hwalk (index : ℕ) (hindex : mode ≤ index) :
        index ≤ trialCount →
          binomialProbabilityMass trialCount index probability ≤
            binomialProbabilityMass trialCount mode probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hstep_down index hindex (by omega)).trans
          (hinduction (by omega))
    exact hwalk successCount habove hsuccess

theorem binomialProbabilityMass_sum_eq_one
    (trialCount : ℕ) (probability : ℝ) :
    (∑ successCount ∈ Finset.range (trialCount + 1),
      binomialProbabilityMass trialCount successCount probability) = 1 := by
  unfold binomialProbabilityMass
  calc
    (∑ successCount ∈ Finset.range (trialCount + 1),
      (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount)) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        probability ^ successCount *
          (1 - probability) ^ (trialCount - successCount) *
          (trialCount.choose successCount : ℝ) := by
            apply Finset.sum_congr rfl
            intro successCount _
            ring
    _ = (probability + (1 - probability)) ^ trialCount :=
      (add_pow probability (1 - probability) trialCount).symm
    _ = 1 := by
      rw [show probability + (1 - probability) = 1 by ring]
      simp

theorem binomialProbabilityMass_mode_ge_inverse
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    1 / ((trialCount + 1 : ℕ) : ℝ) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have hdenominator : 0 < ((trialCount + 1 : ℕ) : ℝ) := by
    positivity
  apply (div_le_iff₀ hdenominator).mpr
  calc
    (1 : ℝ) =
      ∑ successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount successCount
          ((mode : ℝ) / (trialCount : ℝ)) :=
      (binomialProbabilityMass_sum_eq_one
        trialCount ((mode : ℝ) / (trialCount : ℝ))).symm
    _ ≤ ∑ _successCount ∈ Finset.range (trialCount + 1),
        binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) := by
      apply Finset.sum_le_sum
      intro successCount hsuccess
      apply binomialProbabilityMass_le_mode
        trialCount mode successCount hmode
      have hbound := Finset.mem_range.mp hsuccess
      omega
    _ = binomialProbabilityMass trialCount mode
          ((mode : ℝ) / (trialCount : ℝ)) *
        ((trialCount + 1 : ℕ) : ℝ) := by
      simp [nsmul_eq_mul]
      ring

theorem binomialProbabilityMass_mode_mul_exp_entropy
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) *
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((mode : ℝ) / (trialCount : ℝ))) =
      (trialCount.choose mode : ℝ) := by
  by_cases hzero : mode = 0
  · subst mode
    simp [binomialProbabilityMass]
  by_cases hfull : mode = trialCount
  · subst mode
    have htrials : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast hzero
    simp [binomialProbabilityMass, htrials]
  have hmode_pos : 0 < mode := Nat.pos_of_ne_zero hzero
  have hmode_lt : mode < trialCount :=
    lt_of_le_of_ne hmode hfull
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hprobability : 0 < probability := by
    dsimp [probability]
    positivity
  have hprobability_one : probability < 1 := by
    dsimp [probability]
    apply (div_lt_one htrials_real).mpr
    exact_mod_cast hmode_lt
  have hcomplement : 0 < 1 - probability := by
    linarith
  have hproduct :
      0 < probability ^ mode *
        (1 - probability) ^ (trialCount - mode) := by
    positivity
  have hentropy :
      (trialCount : ℝ) * Real.binEntropy probability =
        -(mode : ℝ) * Real.log probability -
          ((trialCount - mode : ℕ) : ℝ) *
            Real.log (1 - probability) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv, Nat.cast_sub hmode]
    dsimp [probability]
    field_simp [htrials_real.ne']
    ring
  have hlog :
      Real.log
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode)) +
        (trialCount : ℝ) * Real.binEntropy probability = 0 := by
    rw [Real.log_mul
      (pow_pos hprobability mode).ne'
      (pow_pos hcomplement (trialCount - mode)).ne',
      Real.log_pow, Real.log_pow, hentropy]
    ring
  change
    binomialProbabilityMass trialCount mode probability *
      Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ)
  calc
    binomialProbabilityMass trialCount mode probability *
        Real.exp ((trialCount : ℝ) * Real.binEntropy probability) =
      (trialCount.choose mode : ℝ) *
        (probability ^ mode *
          (1 - probability) ^ (trialCount - mode) *
          Real.exp ((trialCount : ℝ) * Real.binEntropy probability)) := by
        unfold binomialProbabilityMass
        ring
    _ = (trialCount.choose mode : ℝ) *
        Real.exp
          (Real.log
              (probability ^ mode *
                (1 - probability) ^ (trialCount - mode)) +
            (trialCount : ℝ) * Real.binEntropy probability) := by
          rw [Real.exp_add, Real.exp_log hproduct]
    _ = (trialCount.choose mode : ℝ) := by
      rw [hlog]
      simp

theorem exp_binary_entropy_div_le_choose
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) ≤
      (trialCount.choose successCount : ℝ) := by
  have hmode := binomialProbabilityMass_mode_ge_inverse
    trialCount successCount hcount
  have hexponential :
      0 ≤ Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) :=
    (Real.exp_pos _).le
  calc
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) =
      (1 / ((trialCount + 1 : ℕ) : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) := by
        ring
    _ ≤ binomialProbabilityMass trialCount successCount
          ((successCount : ℝ) / (trialCount : ℝ)) *
        Real.exp
          ((trialCount : ℝ) *
            Real.binEntropy
              ((successCount : ℝ) / (trialCount : ℝ))) :=
      mul_le_mul_of_nonneg_right hmode hexponential
    _ = (trialCount.choose successCount : ℝ) :=
      binomialProbabilityMass_mode_mul_exp_entropy
        trialCount successCount hcount

theorem hammingRetentionProbability_sq_mul_wordCount_eq_exp
    (dimension : ℕ) :
    hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - 2 * midpointBeta) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold hammingRetentionProbability
  rw [hwords, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem hammingBall_card_ge_boundary_binomial
    (dimension radius : ℕ)
    (word : HammingWord dimension) :
    dimension.choose radius ≤ (hammingBall dimension radius word).card := by
  rw [hammingBall_card]
  apply Finset.single_le_sum
    (s := Finset.range (radius + 1))
    (f := fun distance => dimension.choose distance)
  · intro distance _
    exact Nat.zero_le _
  · simp

theorem manuscriptHammingRadius_le_dimension (dimension : ℕ) :
    manuscriptHammingRadius dimension ≤ dimension := by
  have hradius := manuscriptHammingRadius_le dimension
  have hdimension : 0 ≤ (dimension : ℝ) := Nat.cast_nonneg dimension
  have htau := tau_lt_one_half
  have hreal :
      (manuscriptHammingRadius dimension : ℝ) ≤ (dimension : ℝ) := by
    nlinarith
  exact_mod_cast hreal

theorem manuscriptHammingRadius_ratio_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        (manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 tau) := by
  unfold manuscriptHammingRadius
  exact
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) tau_pos.le).comp
      tendsto_natCast_atTop_atTop

theorem manuscriptHammingRadius_binEntropy_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) / (dimension : ℝ)))
      atTop (𝓝 (Real.binEntropy tau)) := by
  exact Real.binEntropy_continuous.continuousAt.tendsto.comp
    manuscriptHammingRadius_ratio_tendsto

theorem manuscriptHammingBall_card_entropy_lower
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
  calc
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((manuscriptHammingRadius dimension : ℝ) /
              (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      (dimension.choose (manuscriptHammingRadius dimension) : ℝ) :=
        exp_binary_entropy_div_le_choose dimension
          (manuscriptHammingRadius dimension)
          (manuscriptHammingRadius_le_dimension dimension)
    _ ≤ ((hammingBall dimension
        (manuscriptHammingRadius dimension) word).card : ℝ) := by
      exact_mod_cast hammingBall_card_ge_boundary_binomial
        dimension (manuscriptHammingRadius dimension) word

theorem eventually_manuscriptHammingRadius_binEntropy_ge
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.binEntropy tau - loss ≤
        Real.binEntropy
          ((manuscriptHammingRadius dimension : ℝ) /
            (dimension : ℝ)) := by
  have hneighborhood :
      Set.Ioi (Real.binEntropy tau - loss) ∈
        𝓝 (Real.binEntropy tau) :=
    Ioi_mem_nhds (by linarith)
  filter_upwards
    [manuscriptHammingRadius_binEntropy_tendsto hneighborhood]
    with dimension hdimension
  exact (show Real.binEntropy tau - loss <
    Real.binEntropy
      ((manuscriptHammingRadius dimension : ℝ) /
        (dimension : ℝ)) from hdimension).le

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp
          ((dimension : ℝ) *
            (sampledHammingEdgeEntropyRate - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        hammingExpectedRetainedEdgeCount dimension
          (manuscriptHammingRadius dimension) := by
  filter_upwards
    [eventually_manuscriptHammingRadius_binEntropy_ge loss hloss]
    with dimension hentropy
  have hdegree :
      Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := manuscriptHammingBall_card_entropy_lower dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp
        ((dimension : ℝ) *
          (sampledHammingEdgeEntropyRate - loss)) /
        ((dimension + 1 : ℕ) : ℝ) =
      (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) * (Real.binEntropy tau - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [hammingRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold sampledHammingEdgeEntropyRate
        ring_nf
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp
          ((dimension : ℝ) *
            Real.binEntropy
              ((manuscriptHammingRadius dimension : ℝ) /
                (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        gcongr
    _ ≤ (hammingRetentionProbability dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈
          Finset.range (manuscriptHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
        gcongr
    _ = hammingExpectedRetainedEdgeCount dimension
        (manuscriptHammingRadius dimension) := by
      rw [hammingExpectedRetainedEdgeCount_eq]
