-- Prove2me | solution 1 for mme_numerical_package_step_boundary_four
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-23T10:18:25.956136+00:00
-- url     : https://prove2.me/submissions/ef3924a6-8916-4714-b47c-92abc42d94e0

import Definitions.Def_mme_entropy_regional_CW_recipe
import Definitions.Def_mme_integer_regional_CW_recipe
import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_recursive_profiled_CW_data
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

open BigOperators

namespace AgentHStepFour

lemma negMulLog_nat_nonpos (k : ℕ) : Real.negMulLog (k : ℝ) ≤ 0 := by
  rcases Nat.eq_zero_or_pos k with h | h
  · simp [h]
  · unfold Real.negMulLog
    have h1 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast h)
    have h2 : (0 : ℝ) ≤ k := by positivity
    nlinarith

lemma massEntropy_nat_le {W : Type*} [Fintype W] (x : W → ℕ) :
    RegionRate.massEntropy (fun w => (x w : ℝ)) ≤
      ((∑ w, x w : ℕ) : ℝ) * (((∑ w, x w : ℕ) : ℝ) - 1) := by
  unfold RegionRate.massEntropy RegionRate.entropy
  beta_reduce
  have h1 : ∑ w, Real.negMulLog (x w : ℝ) ≤ 0 :=
    Finset.sum_nonpos (fun w _ => negMulLog_nat_nonpos _)
  have hS : (∑ w, (x w : ℝ)) = ((∑ w, x w : ℕ) : ℝ) := by push_cast; rfl
  rw [hS]
  have key : -Real.negMulLog ((∑ w, x w : ℕ) : ℝ) ≤
      ((∑ w, x w : ℕ) : ℝ) * (((∑ w, x w : ℕ) : ℝ) - 1) := by
    generalize (∑ w, x w : ℕ) = S
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h; simp
    · have hl : Real.log (S : ℝ) ≤ (S : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by exact_mod_cast h)
      have : (0 : ℝ) ≤ S := by positivity
      simp only [Real.negMulLog]
      nlinarith
  linarith

lemma negMulLog_le_one_of {x : ℝ} (h0 : 0 ≤ x) : Real.negMulLog x ≤ 1 := by
  rcases h0.eq_or_lt with h | h
  · subst h; simp
  · unfold Real.negMulLog
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr h)
    rw [Real.log_inv] at h2
    have h3 : x * (-Real.log x) ≤ x * (x⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 h.le
    rw [mul_sub, mul_inv_cancel₀ h.ne'] at h3
    nlinarith

lemma entropyPenalty_nonneg {half : ℕ} {parent : Fin 3 → ℕ}
    (alpha : RecursiveThinSplit.Split half parent → ℝ)
    (h0 : ∀ a, 0 ≤ alpha a) (h1 : ∑ a, alpha a = 1) :
    0 ≤ RecursiveThinSplit.entropyPenalty alpha := by
  unfold RecursiveThinSplit.entropyPenalty
  have hmem : alpha ∈ RecursiveThinSplit.SameMarginalDistributions alpha :=
    ⟨h0, h1, fun _ _ => rfl⟩
  have hbdd : BddAbove (mme_modern_entropyBits ''
      RecursiveThinSplit.SameMarginalDistributions alpha) := by
    refine ⟨(Fintype.card (RecursiveThinSplit.Split half parent) : ℝ) / Real.log 2, ?_⟩
    rintro z ⟨rho, ⟨hr0, _, _⟩, rfl⟩
    unfold mme_modern_entropyBits
    apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
    calc ∑ a, Real.negMulLog (rho a)
        ≤ ∑ _a : RecursiveThinSplit.Split half parent, (1 : ℝ) :=
          Finset.sum_le_sum (fun a _ => negMulLog_le_one_of (hr0 a))
      _ = _ := by simp
  have := le_csSup hbdd (Set.mem_image_of_mem _ hmem)
  linarith

lemma sum_counts {half n : ℕ} {parent : Fin 3 → ℕ}
    (w : Fin n → RecursiveThinSplit.Split half parent)
    (m : RecursiveThinSplit.Split half parent → ℕ)
    (h : RecursiveThinSplit.HasJointCounts w m) : ∑ a, m a = n := by
  have : ∑ a, m a = ∑ a, RecursiveThinSplit.count w a := by
    apply Finset.sum_congr rfl; intro a _; exact (h a).symm
  rw [this]
  unfold RecursiveThinSplit.count
  rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (w x))]
  simp

lemma entropyLower_lt_one {lower : ℕ} {P : Predicate 4} (S : IntegerStep lower 4 P) :
    S.entropyLower < 1 := by
  -- total number of hash positions is at most 2
  have hcard : S.L = ∑ r, S.n r * 2 := by
    have := Fintype.card_congr S.positions
    simpa [Fintype.card_sigma] using this
  have hT : ∑ r, S.n r ≤ 2 := by
    have hpow : 1 ≤ 2 ^ (lower - 1) := Nat.one_le_two_pow
    have hL : S.L ≤ 4 := by
      have := S.length
      nlinarith
    rw [hcard, ← Finset.sum_mul] at hL
    omega
  have hnr : ∀ r, S.n r ≤ 2 := fun r =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)) hT
  -- joint counts
  have hjc : ∀ r, RecursiveThinSplit.HasJointCounts (S.reference r) (S.m r) := by
    have := S.reference_target
    unfold RecursiveXHash.target at this
    simpa using this
  have hsum : ∀ r, ∑ c, S.m r c = S.n r := fun r => sum_counts _ _ (hjc r)
  -- the rate is at most 2
  have hE : RegionRate.regionalRate S.total S.n S.m S.mu ≤ 2 := by
    unfold RegionRate.regionalRate
    refine le_trans (min_le_left _ _) ?_
    have hpen : 0 ≤ RegionRate.penaltyPotential S.n S.m := by
      unfold RegionRate.penaltyPotential
      apply Finset.sum_nonneg
      intro r _
      rcases Nat.eq_zero_or_pos (S.n r) with h | h
      · simp [h]
      · apply mul_nonneg (mul_nonneg (by positivity) (Real.log_pos one_lt_two).le)
        apply entropyPenalty_nonneg
        · intro a; positivity
        · rw [← Finset.sum_div]
          have : (∑ c, (S.m r c : ℝ)) = (S.n r : ℝ) := by exact_mod_cast hsum r
          rw [this, div_self (by exact_mod_cast h.ne')]
    have hco : RegionRate.coarsePotential S.m 0 ≤ 2 := by
      unfold RegionRate.coarsePotential
      have hterm : ∀ r, RegionRate.massEntropy
          (fun j ↦ (RegionRate.marginalCounts S.m 0 r j : ℝ)) ≤ (S.n r : ℝ) := by
        intro r
        refine le_trans (massEntropy_nat_le _) ?_
        have hm : (∑ j, RegionRate.marginalCounts S.m 0 r j) = S.n r := by
          unfold RegionRate.marginalCounts
          rw [Fintype.sum_fiberwise (fun c : RecursiveThinSplit.Split S.half (S.parent r) => c.val 0)
            (fun c => S.m r c)]
          exact hsum r
        rw [hm]
        have h2 : (S.n r : ℝ) ≤ 2 := by exact_mod_cast hnr r
        have h0 : (0 : ℝ) ≤ S.n r := by positivity
        nlinarith
      calc ∑ r, RegionRate.massEntropy (fun j ↦ (RegionRate.marginalCounts S.m 0 r j : ℝ))
          ≤ ∑ r, (S.n r : ℝ) := Finset.sum_le_sum (fun r _ => hterm r)
        _ ≤ 2 := by exact_mod_cast hT
    linarith
  -- the loss is nonnegative
  have hmod : 0 ≤ RegionRate.entropyModulus
      (Fin 2 → CompleteSplit.CompleteWord lower) S.epsilon := by
    unfold RegionRate.entropyModulus
    apply Real.sSup_nonneg
    rintro z ⟨p, q, _, _, _, rfl⟩
    exact abs_nonneg _
  have hloss : 0 ≤ ((∑ r, S.n r : ℕ) : ℝ) *
      RegionRate.entropyModulus (Fin 2 → CompleteSplit.CompleteWord lower) S.epsilon :=
    mul_nonneg (by positivity) hmod
  -- the denominator is at least 64
  have hpoly : ∀ k : ℕ, (1 : ℝ) ≤ RegionRate.polynomialFactor S.n k := by
    intro k
    unfold RegionRate.polynomialFactor
    apply one_le_pow₀
    have : (0 : ℝ) ≤ ((∑ r, S.n r : ℕ) : ℝ) := by positivity
    linarith
  have hfac : (2 : ℝ) ≤ RegionRate.scaleFactor (half := S.half) (parent := S.parent)
      S.n S.repairScale lower := by
    unfold RegionRate.scaleFactor RegionRate.loadFactor RegionRate.ambientFactor
    have h1 := hpoly (S.R * (S.half + 1))
    have h2 := hpoly (S.R * (S.half + 1) *
      Fintype.card (Fin 2 → CompleteSplit.CompleteWord lower))
    have h3 : (0 : ℝ) ≤ ((((∑ r, S.n r : ℕ) : ℝ) + 1) ^
      Fintype.card (RecursiveYZ.Cell S.half S.R S.parent)) := by positivity
    have h4 : (0 : ℝ) ≤ (S.repairScale : ℝ) := by positivity
    have h5 : (0 : ℝ) ≤ (S.half : ℝ) := by positivity
    have h6 : 0 ≤ 8 * (((∑ r, S.n r : ℕ) : ℝ) + 1) ^
      Fintype.card (RecursiveYZ.Cell S.half S.R S.parent) *
        RegionRate.polynomialFactor S.n (S.R * (S.half + 1)) := by positivity
    have h7 : 0 ≤ 128 * (S.repairScale : ℝ) *
        RegionRate.polynomialFactor S.n (S.R * (S.half + 1)) *
        RegionRate.polynomialFactor S.n (S.R * (S.half + 1) *
          Fintype.card (Fin 2 → CompleteSplit.CompleteWord lower)) := by
      have : (0 : ℝ) ≤ RegionRate.polynomialFactor S.n (S.R * (S.half + 1)) := by linarith
      have : (0 : ℝ) ≤ RegionRate.polynomialFactor S.n (S.R * (S.half + 1) *
          Fintype.card (Fin 2 → CompleteSplit.CompleteWord lower)) := by linarith
      positivity
    linarith
  have hsq : 0 ≤ Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half)
      (parent := S.parent) S.n S.repairScale lower) +
      RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon) := Real.sqrt_nonneg _
  have hexp : Real.exp 2 < 8 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [h]
    have : 0 < Real.exp 1 := Real.exp_pos 1
    nlinarith
  unfold IntegerStep.entropyLower
  simp only []
  rw [div_lt_one (by
    have := hpoly (Fintype.card (RecursiveYZ.Cell S.half S.R S.parent))
    positivity)]
  have hnum : Real.exp (RegionRate.regionalRate S.total S.n S.m S.mu -
      ((∑ r, S.n r : ℕ) : ℝ) *
        RegionRate.entropyModulus (Fin 2 → CompleteSplit.CompleteWord lower) S.epsilon -
      4 * Real.sqrt (Real.log (RegionRate.scaleFactor (half := S.half)
      (parent := S.parent) S.n S.repairScale lower) +
      RegionRate.scaleExponent S.total S.n S.m S.mu S.epsilon)) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    linarith
  have hden : (64 : ℝ) ≤ 32 * RegionRate.polynomialFactor S.n
      (Fintype.card (RecursiveYZ.Cell S.half S.R S.parent)) *
      RegionRate.scaleFactor (half := S.half) (parent := S.parent) S.n S.repairScale lower := by
    have := hpoly (Fintype.card (RecursiveYZ.Cell S.half S.R S.parent))
    nlinarith
  linarith

end AgentHStepFour

theorem solution : ¬ (exists (lower : Nat) (P : Predicate 4) (S : IntegerStep lower 4 P)
    (B : BoundaryEnd lower 4 S.output) (copies : Nat), 0 < copies ∧
    (((copies * 8 ^ S.repairExponent : Nat)) : Real) ≤ S.entropyLower ∧
    390625 ≤ B.a * B.b * B.c) := by
  rintro ⟨lower, P, S, B, copies, hc, hle, -⟩
  have h1 : (1 : ℝ) ≤ ((copies * 8 ^ S.repairExponent : ℕ) : ℝ) := by
    have : 0 < copies * 8 ^ S.repairExponent := by positivity
    exact_mod_cast this
  have := AgentHStepFour.entropyLower_lt_one S
  linarith

